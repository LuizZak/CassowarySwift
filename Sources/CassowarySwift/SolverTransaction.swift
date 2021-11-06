/// Intermediates changes to a `Solver` instance.
public class SolverTransaction {
    private var changes: [Change] = []

    let solver: Solver

    /// Whether this transaction has been cancelled with a call to `cancel`.
    private(set) public var isCancelled: Bool = false

    init(solver: Solver) {
        self.solver = solver
    }

    /// Registers a constraint to be added to the solver.
    public func addConstraint(_ constraint: Constraint) {
        changes.append(.addConstraint(constraint))
    }

    /// Registers a constraint to be removed from the solver.
    public func removeConstraint(_ constraint: Constraint) {
        changes.append(.removeConstraint(constraint))
    }

    /// Registers a variable edit change to the solver, with a given strength.
    public func addEditVariable(variable: Variable, strength: Double) {
        changes.append(.addEditVariable(variable, strength: strength))
    }

    /// Registers a variable edit removal from the solver.
    public func removeEditVariable(_ variable: Variable) {
        changes.append(.removeEditVariable(variable))
    }

    /// Registers a variable value suggestion on the solver.
    public func suggestValue(variable: Variable, value: Double) {
        changes.append(.suggestValue(variable, value: value))
    }

    /// Applies all changes registered on this transaction, in the order that
    /// they where submitted to this transaction.
    ///
    /// Errors are raised according to inconsistent states present on the current
    /// transaction changes.
    ///
    /// If a previous call to `cancel` was made prior to `apply`, changes are
    /// ignored.
    public func apply() throws {
        if isCancelled {
            return
        }

        try solver.setAutoSolve(false)

        for change in changes {
            switch change {
            case .addConstraint(let constraint):
                try solver.addConstraint(constraint)

            case .removeConstraint(let constraint):
                try solver.removeConstraint(constraint)

            case let .addEditVariable(variable, strength: strength):
                try solver.addEditVariable(variable: variable, strength: strength)

            case .removeEditVariable(let variable):
                try solver.removeEditVariable(variable)

            case let .suggestValue(variable, value):
                try solver.suggestValue(variable: variable, value: value)
            }
        }

        try solver.setAutoSolve(true)
    }

    /// Cancels this transaction, dropping all changes to be made.
    ///
    /// Further calls to change the transaction state are ignored.
    public func cancel() {
        isCancelled = true
    }
}

private enum Change {
    case addConstraint(Constraint)
    case removeConstraint(Constraint)
    case addEditVariable(Variable, strength: Double)
    case removeEditVariable(Variable)
    case suggestValue(Variable, value: Double)
}
