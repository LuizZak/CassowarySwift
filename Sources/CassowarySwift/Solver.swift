/*

 Copyright (c) 2017, Tribal Worldwide London
 Copyright (c) 2015, Alex Birkett
 All rights reserved.

 Redistribution and use in source and binary forms, with or without
 modification, are permitted provided that the following conditions are met:

 * Redistributions of source code must retain the above copyright notice, this
 list of conditions and the following disclaimer.

 * Redistributions in binary form must reproduce the above copyright notice,
 this list of conditions and the following disclaimer in the documentation
 and/or other materials provided with the distribution.

 * Neither the name of kiwi-java nor the names of its
 contributors may be used to endorse or promote products derived from
 this software without specific prior written permission.

 THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
 FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
 CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
 OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

 */

public final class Solver {
    internal struct Tag {
        var marker: Symbol
        var other: Symbol?
    }

    internal class EditInfo {
        var tag: Tag
        var constraint: EditConstraint
        var constant: Double

        init(constraint: EditConstraint, tag: Tag, constant: Double) {
            self.constraint = constraint
            self.tag = tag
            self.constant = constant
        }
    }

    private var autoSolve: Bool = true
    private var nextSymbolId: Int = 0
    private var constraintDict: [Constraint: Tag] = [:]
    private var rows = SymbolOrderedDictionary<Row>()
    private var variableSymbols: [Variable: (Symbol, refCount: Int)] = [:]
    private var infeasibleRows = [Symbol]()
    private var objective = Row()
    private var artificial: Row?

    private(set) var variableEditInfo: [Variable: EditInfo] = [:]

    var variables: [Variable] {
        return Array(variableSymbols.keys)
    }

    var constraints: [Constraint] {
        return Array(constraintDict.keys)
    }

    // MARK: Initializers

    public init() {

    }

    /// If `true`, automatically optimizes the solver after each constraint
    /// added, and if `false`, the system is not automatically optimized until
    /// `setAutoSolve(true)` is invoked.
    ///
    /// The solver starts with auto-solve on by default.
    public func setAutoSolve(_ autoSolve: Bool) throws {
        if !self.autoSolve && autoSolve {
            try optimize(objective: objective)
            try dualOptimize()
        }

        self.autoSolve = autoSolve
    }

    /// Starts a new solver transaction and returns the transaction object.
    public func startTransaction() -> SolverTransaction {
        return SolverTransaction(solver: self)
    }

    /// Starts a new solver transaction, invoking the block with the transaction
    /// instance before applying all changes, if the transaction has not been
    /// cancelled before the end of the block.
    public func withTransaction(_ block: (SolverTransaction) -> Void) throws {
        let transaction = startTransaction()

        block(transaction)

        try transaction.apply()
    }

    /**
     Update the values of the external solver variables.
     */
    public func updateVariables() {
        for (variable, (symbol, _)) in variableSymbols {
            if let row = rows[symbol] {
                variable.value = row.constant
            } else {
                variable.value = 0
            }
        }
    }

    /// Returns a string representing the internal state of the solver.
    public func stateDescription() -> String {
        var string = ""

        for row in rows {
            string += "\(row.key) = \(row.value)\n"
        }

        return string.trimmingCharacters(in: .whitespacesAndNewlines)
    }

    /// Iterates over all variable -> symbol references removing any variable
    /// entry that is no longer referenced by any constraint on this solver.
    internal func flushUnusedVariables() {
        for (variable, (_, refCount)) in variableSymbols where refCount <= 0 {
            variableSymbols.removeValue(forKey: variable)
        }
    }

    @discardableResult
    internal func addConstraint(_ constraint: Constraint) throws -> Tag {
        if hasConstraint(constraint) {
            throw CassowaryError.duplicateConstraint(constraint)
        }

        let (row, tag) = createRow(constraint: constraint)

        if let subject = try getSubject(constraint: constraint, row: row, tag: tag) {
            row.solveFor(subject)
            substitute(symbol: subject, row: row)
            rows[subject] = row
        }

        constraintDict[constraint] = tag

        if autoSolve {
            try optimize(objective: objective)
        }

        return tag
    }

    /// Remove a constraint from the solver
    internal func removeConstraint(_ constraint: Constraint) throws {
        guard let tag = constraintDict.removeValue(forKey: constraint) else {
            throw CassowaryError.unknownConstraint(constraint)
        }

        for term in constraint.expression.terms where !term.coefficient.isNearZero {
            let variable = term.variable

            variableSymbols[variable]?.refCount -= 1
        }

        removeConstraintEffects(constraint: constraint, tag: tag)
        if rows.removeValue(forKey: tag.marker) == nil {
            guard let (leaving, row) = getMarkerLeavingRow(marker: tag.marker) else {
                throw CassowaryError.internalSolver("Internal solver error")
            }

            rows.removeValue(forKey: leaving)
            row.solveFor(leaving, tag.marker)
            substitute(symbol: tag.marker, row: row)
        }

        if autoSolve {
            try optimize(objective: objective)
        }
    }

    /// Check if the solver has a constraint
    internal func hasConstraint(_ constraint: Constraint) -> Bool {
        return constraintDict[constraint] != nil
    }

    /**
     Add an edit constraint on the provided variable, so that suggestValue can be used on it.
     - parameters:
         - variable: The Variable to add the edit constraint on
         - strength: The strength of the constraint to add. This cannot be "Required".
     */
    internal func addEditVariable(variable: Variable, strength: Double) throws {
        guard variableEditInfo[variable] == nil else {
            throw CassowaryError.duplicateEditVariable
        }

        let clippedStrength = Strength.clip(strength)

        if clippedStrength == Strength.REQUIRED {
            throw CassowaryError.requiredFailure
        }

        let constraint =
            EditConstraint(
                expr: Expression(term: Term(variable: variable)),
                op: .equal,
                strength: clippedStrength
            )

        do {
            let tag = try addConstraint(constraint)

            let info = EditInfo(constraint: constraint, tag: tag, constant: 0.0)
            variableEditInfo[variable] = info
        } catch let error as CassowaryError {
            print(error)
        }
    }

    /**
     Remove an edit constraint on the provided variable.
     Throws an error if the variable does not have an edit constraint
     */
    internal func removeEditVariable(_ variable: Variable) throws {
        guard let edit = variableEditInfo.removeValue(forKey: variable) else {
            throw CassowaryError.unknownEditVariable
        }

        do {
            try removeConstraint(edit.constraint)
        } catch {
            print(error)
        }
    }

    /// Checks if the solver has an edit constraint for the provided variable.
    internal func hasEditVariable(_ variable: Variable) -> Bool {
        return variableEditInfo[variable] != nil
    }

    /**
     Specify a desired value for the provided variable.
     The variable needs to have been previously added as an edit variable.
     Throws an error if the provided variable has not been previously added as an edit variable.
     */
    internal func suggestValue(variable: Variable, value: Double) throws {
        guard let info = variableEditInfo[variable] else {
            throw CassowaryError.unknownEditVariable
        }

        let delta = value - info.constant
        info.constant = value
        info.constraint.suggestedValue = value

        // Check first if the positive error variable is basic.
        if let row = rows[info.tag.marker] {
            if row.add(-delta) < 0.0 {
                infeasibleRows.append(info.tag.marker)
            }

            if autoSolve {
                try dualOptimize()
            }

            return
        }

        // Check next if the negative error variable is basic.
        if let otherTag = info.tag.other, let row = rows[otherTag] {
            if row.add(delta) < 0.0 {
                infeasibleRows.append(otherTag)
            }

            if autoSolve {
                try dualOptimize()
            }

            return
        }

        // Otherwise update each row where the error variables exist.
        for (s, row) in rows {
            let coefficient = row.coefficientFor(info.tag.marker)
            if coefficient != 0.0 && row.add(delta * coefficient) < 0.0 && s.symbolType != .external {
                infeasibleRows.append(s)
            }
        }

        if autoSolve {
            try dualOptimize()
        }
    }

    private func getSubject(constraint: Constraint, row: Row, tag: Tag) throws -> Symbol? {
        if let subject = chooseSubject(row: row, tag: tag) {
            return subject
        }

        if row.allDummies() {
            if !row.constant.isNearZero {
                throw CassowaryError.unsatisfiableConstraint(constraint, Array(constraintDict.keys))
            } else {
                return tag.marker
            }
        }

        if try !addWithArtificialVariable(row: row) {
            throw CassowaryError.unsatisfiableConstraint(constraint, Array(constraintDict.keys))
        }

        return nil
    }

    private func removeConstraintEffects(constraint: Constraint, tag: Tag) {
        if tag.marker.symbolType == .error {
            removeMarkerEffects(marker: tag.marker, strength: constraint.strength)
        } else if let other = tag.other, other.symbolType == .error {
            removeMarkerEffects(marker: other, strength: constraint.strength)
        }
    }

    private func removeMarkerEffects(marker: Symbol, strength: Double) {
        if let row = rows[marker] {
            objective.insert(other: row, coefficient: -strength)
        } else {
            objective.insert(symbol: marker, coefficient: -strength)
        }
    }

    private func getMarkerLeavingRow(marker: Symbol) -> (Symbol, Row)? {
        let dMax = Double.greatestFiniteMagnitude
        var r1 = dMax
        var r2 = dMax

        var first: (Symbol, Row)?
        var second: (Symbol, Row)?
        var third: (Symbol, Row)?

        for (s, candidateRow) in rows {
            let c = candidateRow.coefficientFor(marker)

            if c == 0.0 {
                continue
            }

            let r = candidateRow.constant / c

            if s.symbolType == .external {
                third = (s, candidateRow)
            } else if c < 0.0 {
                if -r < r1 {
                    r1 = -r
                    first = (s, candidateRow)
                }
            } else {
                if r < r2 {
                    r2 = r
                    second = (s, candidateRow)
                }
            }
        }

        if first != nil {
            return first
        }

        if second != nil {
            return second
        }

        return third
    }

    /**
     * Create a new Row object for the given constraint.
     * <p/>
     * The terms in the constraint will be converted to cells in the row.
     * Any term in the constraint with a coefficient of zero is ignored.
     * This method uses the `getVarSymbol` method to get the symbol for
     * the variables added to the row. If the symbol for a given cell
     * variable is basic, the cell variable will be substituted with the
     * basic row.
     * <p/>
     * The necessary slack and error variables will be added to the row.
     * If the constant for the row is negative, the sign for the row
     * will be inverted so the constant becomes positive.
     * <p/>
     * The tag will be updated with the marker and error symbols to use
     * for tracking the movement of the constraint in the tableau.
     */
    private func createRow(constraint: Constraint) -> (Row, Tag) {
        let expression = constraint.expression
        let row = Row(constant: expression.constant)

        var marker: Symbol
        var other: Symbol?

        for term in expression.terms where !term.coefficient.isNearZero {
            let symbol = createVarSymbol(term.variable)

            if let otherRow = rows[symbol] {
                row.insert(other: otherRow, coefficient: term.coefficient)
            } else {
                row.insert(symbol: symbol, coefficient: term.coefficient)
            }
        }

        switch constraint.op {
        case .greaterThanOrEqual, .lessThanOrEqual:
            let coeff = constraint.op == .lessThanOrEqual ? 1.0 : -1.0
            let slack = createSymbol(type: .slack)
            marker = slack
            row.insert(symbol: slack, coefficient: coeff)

            if constraint.strength < Strength.REQUIRED {
                let error = createSymbol(type: .error)
                other = error
                row.insert(symbol: error, coefficient: -coeff)
                objective.insert(symbol: error, coefficient: constraint.strength)
            }
        case .equal:
            if constraint.strength < Strength.REQUIRED {
                let errPlus = createSymbol(type: .error)
                let errMinus = createSymbol(type: .error)
                marker = errPlus
                other = errMinus
                row.insert(symbol: errPlus, coefficient: -1.0) // v = ePlus - eMinus
                row.insert(symbol: errMinus, coefficient: 1.0) // v - ePlus + eMinus = 0
                objective.insert(symbol: errPlus, coefficient: constraint.strength)
                objective.insert(symbol: errMinus, coefficient: constraint.strength)
            } else {
                let dummy = createSymbol(type: .dummy)
                marker = dummy
                row.insert(symbol: dummy)
            }
        }

        // Ensure the row as a positive constant.
        if row.constant < 0.0 {
            row.reverseSign()
        }

        return (row, Tag(marker: marker, other: other))
    }

    /**
     Choose the subject for solving for the row

     This method will choose the best subject for using as the solve
     target for the row. An invalid symbol will be returned if there
     is no valid target.
     The symbols are chosen according to the following precedence:
     1) The first symbol representing an external variable.
     2) A negative slack or error tag variable.
     If a subject cannot be found, an invalid symbol will be returned.
     */
    private func chooseSubject(row: Row, tag: Tag) -> Symbol? {
        for key in row.cells.keys {
            if key.symbolType == .external {
                return key
            }
        }

        if tag.marker.symbolType == .slack || tag.marker.symbolType == .error {
            if row.coefficientFor(tag.marker) < 0.0 {
                return tag.marker
            }
        }
        if let other = tag.other, other.symbolType == .slack || other.symbolType == .error {
            if row.coefficientFor(other) < 0.0 {
                return other
            }
        }

        return nil
    }

    /**
     * Add the row to the tableau using an artificial variable.
     * <p/>
     * This will return false if the constraint cannot be satisfied.
     */
    private func addWithArtificialVariable(row: Row) throws -> Bool {
        // Create and add the artificial variable to the tableau
        let art = createSymbol(type: .slack)
        rows[art] = Row(row)

        let artificial = Row(row)
        self.artificial = artificial

        // Optimize the artificial objective. This is successful
        // only if the artificial objective is optimized to zero.
        try optimize(objective: artificial)

        let success = artificial.constant.isNearZero
        self.artificial = nil

        // If the artificial variable is basic, pivot the row so that
        // it becomes basic. If the row is constant, exit early.

        if let rowPtr = rows.removeValue(forKey: art) {
            if rowPtr.cells.count == 0 {
                return success
            }

            guard let entering = rowPtr.anyPivotableSymbol() else {
                return false // unsatisfiable (will this ever happen?)
            }

            rowPtr.solveFor(art, entering)
            substitute(symbol: entering, row: rowPtr)
            rows[entering] = rowPtr
        }

        // Remove the artificial variable from the tableau.
        for row in rows.values {
            row.remove(symbol: art)
        }

        objective.remove(symbol: art)

        return success
    }

    /**
     Substitute the parametric symbol with the given row.

     This method will substitute all instances of the parametric symbol
     in the tableau and the objective function with the given row.
     */
    private func substitute(symbol: Symbol, row: Row) {
        for rowEntry in rows {
            rowEntry.value.substitute(symbol: symbol, row: row)

            if rowEntry.key.symbolType != .external && rowEntry.value.constant < 0.0 {
                infeasibleRows.append(rowEntry.key)
            }
        }

        objective.substitute(symbol: symbol, row: row)

        if let artificial = artificial {
            artificial.substitute(symbol: symbol, row: row)
        }
    }

    /**
     Optimize the system for the given objective function.

     This method performs iterations of Phase 2 of the simplex method
     until the objective function reaches a minimum.
     */
    private func optimize(objective: Row) throws {
        while true {
            guard let entering = objective.getEnteringSymbol() else {
                return
            }

            guard let (leaving, entry) = getLeavingRow(entering) else {
                throw CassowaryError.internalSolver("The objective is unbounded.")
            }

            rows.removeValue(forKey: leaving)
            entry.solveFor(leaving, entering)
            substitute(symbol: entering, row: entry)
            rows[entering] = entry
        }
    }

    private func dualOptimize() throws {
        while let leaving = infeasibleRows.popLast() {
            guard let row = rows[leaving], row.constant < 0.0 else {
                continue
            }
            guard let entering = getDualEnteringSymbol(row) else {
                throw CassowaryError.internalSolver("Internal solver error")
            }

            rows.removeValue(forKey: leaving)
            row.solveFor(leaving, entering)
            substitute(symbol: entering, row: row)
            rows[entering] = row
        }
    }

    private func getDualEnteringSymbol(_ row: Row) -> Symbol? {
        var entering: Symbol?

        var ratio = Double.greatestFiniteMagnitude

        for (s, currentCell) in row.cells where s.symbolType != .dummy && currentCell > 0.0 {
            let coefficient = objective.coefficientFor(s)
            let r = coefficient / currentCell
            if r < ratio {
                ratio = r
                entering = s
            }
        }

        return entering
    }

    /**
     Compute the row which holds the exit symbol for a pivot.

     This documentation is copied from the C++ version and is outdated

     This method will return an iterator to the row in the row map
     which holds the exit symbol. If no appropriate exit symbol is
     found, `nil` will be returned. This indicates that
     the objective function is unbounded.
     */
    private func getLeavingRow(_ entering: Symbol) -> (Symbol, Row)? {
        var ratio = Double.greatestFiniteMagnitude
        var row: (Symbol, Row)?

        for (key, candidateRow) in rows where key.symbolType != .external {
            let temp = candidateRow.coefficientFor(entering)
            guard temp < 0 else {
                continue
            }

            let tempRatio = -candidateRow.constant / temp
            if tempRatio < ratio {
                ratio = tempRatio
                row = (key, candidateRow)
            }
        }

        return row
    }

    /// Creates a new symbol for a given variable.
    ///
    /// If a symbol already exists for the given variable, the reference count
    /// for the variable gets incremented and the existing is returned.
    private func createVarSymbol(_ variable: Variable) -> Symbol {
        if let (symbol, refCount) = variableSymbols[variable] {
            variableSymbols[variable]!.refCount = refCount + 1
            return symbol
        } else {
            let symbol = createSymbol(type: .external)
            variableSymbols[variable] = (symbol, 1)
            return symbol
        }
    }

    private func createSymbol(type: SymbolType) -> Symbol {
        nextSymbolId = nextSymbolId &+ 1
        return Symbol(id: nextSymbolId, symbolType: type)
    }
}
