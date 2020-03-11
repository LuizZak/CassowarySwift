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

    private class Tag {
        var marker: Symbol
        var other: Symbol?
        
        init(marker: Symbol) {
            self.marker = marker
        }
    }

    private class EditInfo {
        var tag: Tag
        var constraint: EditConstraint
        var constant: Double

        public init(constraint: EditConstraint, tag: Tag, constant: Double){
            self.constraint = constraint
            self.tag = tag
            self.constant = constant
        }
    }

    private var nextSymbolId: Int = 0
    private var constraintDict: [Constraint: Tag] = [:]
    private var rows = OrderedDictionary<Symbol, Row>()
    private var variableSymbols: [Variable: Symbol] = [:]
    private var variableEditInfo: [Variable: EditInfo] = [:]
    private var infeasibleRows = [Symbol]()
    private var objective = Row()
    private var artificial: Row?
    
    // MARK: Initializers
    
    public init() {
        
    }

    /// Add a constraint to the solver.
    public func addConstraint(_ constraint: Constraint) throws {
        if constraintDict[constraint] != nil {
            throw CassowaryError.duplicateConstraint(constraint)
        }

        let tag = Tag(marker: createSymbol())
        let row = createRow(constraint: constraint, tag: tag)
        var subject = chooseSubject(row: row, tag: tag)

        if subject.symbolType == .invalid && Solver.allDummies(row: row) {
            if !row.constant.isNearZero {
                throw CassowaryError.unsatisfiableConstraint(constraint, Array(constraintDict.keys))
            } else {
                subject = tag.marker
            }
        }

        if subject.symbolType == .invalid {
            if try !addWithArtificialVariable(row: row) {
                throw CassowaryError.unsatisfiableConstraint(constraint, Array(constraintDict.keys))
            }
        } else {
            row.solveFor(subject)
            substitute(symbol: subject, row: row)
            rows[subject] = row
        }

        constraintDict[constraint] = tag

        try optimize(objective: objective)
    }
    
    /// Remove a constraint from the solver
    public func removeConstraint(_ constraint: Constraint) throws {
        guard let tag = constraintDict[constraint] else {
            throw CassowaryError.unknownConstraint(constraint)
        }

        constraintDict[constraint] = nil
        removeConstraintEffects(constraint: constraint, tag: tag)
        if rows.removeValue(forKey: tag.marker) == nil {
            guard let row = getMarkerLeavingRow(marker: tag.marker) else {
                throw CassowaryError.internalSolver("Internal solver error")
            }

            var leaving: Symbol?
            for (s, r) in rows.orderedEntries {
                if r == row {
                    leaving = s
                }
            }

            if let leaving = leaving {
                rows[leaving] = nil
                row.solveFor(leaving, tag.marker)
                substitute(symbol: tag.marker, row: row)
            } else {
                throw CassowaryError.internalSolver("Internal solver error")
            }
        }

        try optimize(objective: objective)
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

    private func getMarkerLeavingRow(marker: Symbol) -> Row? {
        let dmax = Double.greatestFiniteMagnitude
        var r1 = dmax
        var r2 = dmax

        var first: Row?
        var second: Row?
        var third: Row?

        for (s, candidateRow) in rows.orderedEntries {
            let c = candidateRow.coefficientFor(marker)

            if c == 0.0 {
                continue
            }

            if s.symbolType == .external {
                third = candidateRow
            } else if c < 0.0 {
                let r = -candidateRow.constant / c
                if r < r1 {
                    r1 = r
                    first = candidateRow
                }
            } else {
                let r = candidateRow.constant / c
                if r < r2 {
                    r2 = r
                    second = candidateRow
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
    
    /// Check if the solver has a constraint
    public func hasConstraint(_ constraint: Constraint) -> Bool {
        return constraintDict[constraint] != nil
    }
    
    /**
     Add an edit constraint on the provided variable, so that suggestValue can be used on it.
     - parameters:
         - variable: The Variable to add the edit constraint on
         - strength: The strength of the constraint to add. This cannot be "Required".
     */
    public func addEditVariable(variable: Variable, strength: Double) throws {
        guard variableEditInfo[variable] == nil else {
            throw CassowaryError.duplicateEditVariable
        }

        let clippedStrength = Strength.clip(strength)

        if clippedStrength == Strength.REQUIRED {
            throw CassowaryError.requiredFailure
        }

        var terms = [Term]()
        terms.append(Term(variable: variable))
        let constraint = EditConstraint(expr: Expression(terms: terms), op: .equal, strength: clippedStrength)

        do {
            try addConstraint(constraint)
        } catch let error as CassowaryError {
            print(error)
        }

        // TODO: Check if tag can be nil
        let info = EditInfo(constraint: constraint, tag: constraintDict[constraint]!, constant: 0.0)
        variableEditInfo[variable] = info
    }
    
    /**
     Remove an edit constraint on the provided variable.
     Throws an error if the variable does not have an edit constraint
     */
    public func removeEditVariable(_ variable: Variable) throws {
        guard let edit = variableEditInfo[variable] else {
            throw CassowaryError.unknownEditVariable
        }

        do {
            try removeConstraint(edit.constraint)
        } catch {
            print(error)
        }

        variableEditInfo[variable] = nil
    }
    
    /// Checks if the solver has an edit constraint for the provided variable.
    public func hasEditVariable(_ variable: Variable) -> Bool {
        return variableEditInfo[variable] != nil
    }
    
    /**
     Specify a desired value for the provided variable.
     The variable needs to have been previously added as an edit variable.
     Throws an error if the provided variable has not been previously added as an edit variable.
     */
    public func suggestValue(variable: Variable, value: Double) throws {
        guard let info = variableEditInfo[variable] else {
            throw CassowaryError.unknownEditVariable
        }

        let delta = value - info.constant
        info.constant = value

        var row = rows[info.tag.marker]
        
        info.constraint.suggestedValue = value

        if let row = row {
            if row.add(-delta) < 0.0 {
                infeasibleRows.append(info.tag.marker)
            }
            try dualOptimize()
            return
        }

        if let otherTag = info.tag.other {
            row = rows[otherTag]

            if let row = row {
                if row.add(delta) < 0.0 {
                    infeasibleRows.append(otherTag)
                }
                try dualOptimize()
                return
            }
        }

        for (s, row) in rows.orderedEntries {
            let coefficient = row.coefficientFor(info.tag.marker)
            if coefficient != 0.0 && row.add(delta * coefficient) < 0.0 && s.symbolType != .external {
                infeasibleRows.append(s)
            }
        }

        try dualOptimize()
    }

    /**
     Update the values of the external solver variables.
     */
    public func updateVariables() {
        for (variable, value) in variableSymbols {
            if let row = rows[value] {
                variable.value = row.constant
            } else {
                variable.value = 0
            }
        }
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
    private func createRow(constraint: Constraint, tag: Tag) -> Row {
        let expression = constraint.expression
        let row = Row(constant: expression.constant)

        for term in expression.terms {
            if !term.coefficient.isNearZero {
                let symbol = getVarSymbol(term.variable)

                if let otherRow = rows[symbol] {
                    row.insert(other: otherRow, coefficient: term.coefficient)
                } else {
                    row.insert(symbol: symbol, coefficient: term.coefficient)
                }
            }
        }

        switch constraint.op {
        case .greaterThanOrEqual, .lessThanOrEqual:
            let coeff = constraint.op == .lessThanOrEqual ? 1.0 : -1.0
            let slack = createSymbol(type: .slack)
            tag.marker = slack
            row.insert(symbol: slack, coefficient: coeff)

            if constraint.strength < Strength.REQUIRED {
                let error = createSymbol(type: .error)
                tag.other = error
                row.insert(symbol: error, coefficient: -coeff)
                objective.insert(symbol: error, coefficient: constraint.strength)
            }
        case .equal:
            if constraint.strength < Strength.REQUIRED {
                let errplus = createSymbol(type: .error)
                let errminus = createSymbol(type: .error)
                tag.marker = errplus
                tag.other = errminus
                row.insert(symbol: errplus, coefficient: -1.0) // v = eplus - eminus
                row.insert(symbol: errminus, coefficient: 1.0) // v - eplus + eminus = 0
                objective.insert(symbol: errplus, coefficient: constraint.strength)
                objective.insert(symbol: errminus, coefficient: constraint.strength)
            } else {
                let dummy = createSymbol(type: .dummy)
                tag.marker = dummy
                row.insert(symbol: dummy)
            }
        }

        // Ensure the row as a positive constant.
        if row.constant < 0.0 {
            row.reverseSign()
        }

        return row
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
    private func chooseSubject(row: Row, tag: Tag) -> Symbol {

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
        if tag.other != nil && (tag.other!.symbolType == .slack || tag.other!.symbolType == .error) {
            if row.coefficientFor(tag.other!) < 0.0 {
                return tag.other!
            }
        }

        return createSymbol()
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

        artificial = Row(row)

        // Optimize the artificial objective. This is successful
        // only if the artificial objective is optimized to zero.
        try optimize(objective: artificial!)
        let success = artificial!.constant.isNearZero
        artificial = nil

        // If the artificial variable is basic, pivot the row so that
        // it becomes basic. If the row is constant, exit early.

        if let rowptr = rows[art] {
            var deleteQueue = [Symbol]()
            for s in rows.keys {
                if rows[s]! == rowptr {
                    deleteQueue.append(s)
                }
            }

            while !deleteQueue.isEmpty {
                rows[deleteQueue.popLast()!] = nil
            }

            deleteQueue.removeAll()

            if rowptr.cells.count == 0 {
                return success
            }

            let entering = anyPivotableSymbol(rowptr)
            if entering.symbolType == .invalid {
                return false // unsatisfiable (will this ever happen?)
            }

            rowptr.solveFor(art, entering)
            substitute(symbol: entering, row: rowptr)
            rows[entering] = rowptr
        }

        // Remove the artificial variable from the tableau.
        for (_, row) in rows.orderedEntries {
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
        for rowEntry in rows.orderedEntries {
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
            let entering = getEnteringSymbol(objective)
            if entering.symbolType == .invalid {
                return
            }

            guard let entry = getLeavingRow(entering) else {
                throw CassowaryError.internalSolver("The objective is unbounded.")
            }

            var leaving: Symbol?
            var entryKey: Symbol?

            for (key, row) in rows.orderedEntries where row == entry {
                leaving = key
                entryKey = key
            }

            rows.removeValue(forKey: entryKey!)
            entry.solveFor(leaving!, entering)
            substitute(symbol: entering, row: entry)
            rows[entering] = entry
        }
    }

    private func dualOptimize() throws {
        while let leaving = infeasibleRows.popLast() {
            if let row = rows[leaving], row.constant < 0.0 {
                let entering = getDualEnteringSymbol(row)
                if entering.symbolType == .invalid {
                    throw CassowaryError.internalSolver("Internal solver error")
                }

                rows[leaving] = nil
                row.solveFor(leaving, entering)
                substitute(symbol: entering, row: row)
                rows[entering] = row
            }
        }
    }


    /**
     * Compute the entering variable for a pivot operation.
     * <p/>
     * This method will return first symbol in the objective function which
     * is non-dummy and has a coefficient less than zero. If no symbol meets
     * the criteria, it means the objective function is at a minimum, and an
     * invalid symbol is returned.
     */
    private func getEnteringSymbol(_ objective: Row) -> Symbol {
        for cell in objective.cells.orderedEntries {
            if cell.key.symbolType != .dummy && cell.value < 0.0 {
                return cell.key
            }
        }

        return createSymbol()
    }

    private func getDualEnteringSymbol(_ row: Row) -> Symbol {
        var entering = createSymbol()

        var ratio = Double.greatestFiniteMagnitude

        for (s, currentCell) in row.cells.orderedEntries where s.symbolType != .dummy && currentCell > 0.0 {
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
     Get the first Slack or Error symbol in the row.

     sIf no such symbol is present, and Invalid symbol will be returned.
     */
    private func anyPivotableSymbol(_ row: Row) -> Symbol {
        var symbol: Symbol?

        for entry in row.cells.orderedEntries {
            if entry.key.symbolType == .slack || entry.key.symbolType == .error {
                symbol = entry.key
            }
        }

        if symbol == nil {
            symbol = createSymbol()
        }

        return symbol!
    }

    /**
     Compute the row which holds the exit symbol for a pivot.

     This documentation is copied from the C++ version and is outdated

     This method will return an iterator to the row in the row map
     which holds the exit symbol. If no appropriate exit symbol is
     found, the end() iterator will be returned. This indicates that
     the objective function is unbounded.
     */
    private func getLeavingRow(_ entering: Symbol) -> Row? {
        var ratio = Double.greatestFiniteMagnitude
        var row: Row?

        for key in rows.keys {
            if key.symbolType != .external {
                let candidateRow = rows[key]!
                let temp = candidateRow.coefficientFor(entering)
                if temp < 0 {
                    let tempRatio = -candidateRow.constant / temp
                    if tempRatio < ratio {
                        ratio = tempRatio
                        row = candidateRow
                    }
                }
            }
        }

        return row
    }

    /**
     * Get the symbol for the given variable.
     * <p/>
     * If a symbol does not exist for the variable, one will be created.
     */
    private func getVarSymbol(_ variable: Variable) -> Symbol {
        if let symbol = variableSymbols[variable] {
            return symbol
        } else {
            let symbol = createSymbol(type: .external)
            variableSymbols[variable] = symbol
            return symbol
        }
    }
    
    private func createSymbol(type: Symbol.SymbolType = .invalid) -> Symbol {
        nextSymbolId = nextSymbolId &+ 1
        return Symbol(id: nextSymbolId, type)
    }

    /**
     Test whether a row is composed of all dummy variables.
     */
    private static func allDummies(row: Row) -> Bool {
        return row.cells.dictionary.keys.allSatisfy { $0.symbolType == .dummy }
    }
}
