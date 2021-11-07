import Foundation

// TODO: Handle nil-named variables better.

/// Exposes serialization functionality that can serialize and deserialize
/// constraints on a solver.
public enum SolverSerializer {
    /// Serializes the constraints on the underlying solver and returns the data
    /// for a UTF-8-formatted JSON string with the constraint data.
    public static func serialize(solver: Solver) throws -> Data {
        let serialized = try _serialize(solver: solver)
        let encoder = JSONEncoder()

        return try encoder.encode(serialized)
    }

    /// Deserializes data from a solver from JSON-formatted data.
    public static func deserialize(data: Data, options: DeserializingOptions = .init()) throws -> (Solver, [Variable]) {
        let decoder = JSONDecoder()
        let json = try decoder.decode(JSON.self, from: data)

        let solver = Solver()
        let transaction = solver.startTransaction()

        // Extract variables
        let variablesDict =
        try Dictionary(json[path: "variables"].decode([Variable].self).map { ($0.name, $0) }) {
            if !options.allowDuplicatedVariables {
                throw Error.duplicatedVariableName($1.name)
            }

            return $1
        }

        // Extract edit variable information
        var visitedVariableNames: Set<String> = []
        for editInfo in try json[path: "varEdit"].array {
            let variableName = try editInfo[path: "variable"].string
            let constant = try editInfo[path: "constant"].number
            let strength = try editInfo[path: "strength"].number

            guard let variable = variablesDict[variableName] else {
                throw Error.undefinedVariable(variableName)
            }

            // Avoid duplicated visits to variable edits
            if options.allowDuplicatedVariables {
                if !visitedVariableNames.insert(variableName).inserted {
                    continue
                }
            }

            transaction.addEditVariable(variable, strength: strength)
            transaction.suggestValue(variable, value: constant)
        }

        // Extract constraints
        for constraint in try json[path: "constraints"].array {
            transaction.addConstraint(try deserializeConstraint(constraint, { variablesDict[$0] }))
        }

        try transaction.apply()

        solver.updateVariables()

        return (solver, variablesDict.values.sorted { $0.name < $1.name })
    }

    /// Serializes the changes encoded in a transaction.
    public static func serialize(transaction: SolverTransaction) throws -> Data {
        var data: [JSON] = []

        for change in transaction.changes {
            let changeJson: JSON

            switch change {
            case .addConstraint(let c):
                changeJson = [
                    "change": "addConstraint",
                    "constraint": try _serialize(constraint: c)
                ]

            case .removeConstraint(let c):
                changeJson = [
                    "change": "removeConstraint",
                    "constraint": try _serialize(constraint: c)
                ]

            case .addEditVariable(let v, let strength):
                changeJson = [
                    "change": "addEditVariable",
                    "variable": v.name.json,
                    "strength": strength.json
                ]

            case .suggestValue(let v, let value):
                changeJson = [
                    "change": "suggestValue",
                    "variable": v.name.json,
                    "value": value.json
                ]

            case .removeEditVariable(let v):
                changeJson = [
                    "change": "removeEditVariable",
                    "variable": v.name.json
                ]
            }

            data.append(changeJson)
        }

        let encoder = JSONEncoder()

        return try encoder.encode(data)
    }

    /// Deserializes previously serialized transaction data.
    /// This method assumes all variables referenced by the data have been
    /// referenced before in the solver, otherwise creating them as needed.
    public static func deserialize(data: Data, transaction: SolverTransaction) throws {
        let solver = transaction.solver

        var existingVars = Dictionary(solver.variables.map { ($0.name, $0) }) { $1 }

        /// Resolves a variable from a referenced constraint, returning an
        /// existing variable from the transaction's solver, or the current list
        /// of created variables.
        /// If no variable with a matching name was found, `nil` is returned,
        /// instead.
        func _resolveExistingVar(name: String) -> Variable? {
            return existingVars[name]
        }

        /// Resolves a variable from a referenced constraint, returning an
        /// existing variable from the transaction's solver, if available.
        /// If not found, a new variable will be created.
        func _resolveOrCreateVar(name: String) -> Variable {
            if let existing = _resolveExistingVar(name: name) {
                return existing
            }
            let new = Variable(name)
            existingVars[name] = new
            return new
        }

        let decoder = JSONDecoder()
        let changes = try decoder.decode([JSON].self, from: data)

        outerLoop:
        for change in changes {
            switch try change[path: "change"].string {
            case "addConstraint":
                let constraint = try deserializeConstraint(change[path: "constraint"].json, _resolveOrCreateVar)

                transaction.addConstraint(constraint)

            case "removeConstraint":
                let constraint = try deserializeConstraint(change[path: "constraint"].json, _resolveOrCreateVar)

                for current in solver.constraints {
                    if constraint.isEquivalent(to: current) {
                        transaction.removeConstraint(current)
                        continue outerLoop
                    }
                }

                throw Error.removeConstraintNotFound(constraint)

            case "addEditVariable":
                let variableName = try change[path: "variable"].string
                let strength = try change[path: "strength"].number

                let variable = _resolveOrCreateVar(name: variableName)

                transaction.addEditVariable(variable, strength: strength)

            case "suggestValue":
                let variableName = try change[path: "variable"].string
                let value = try change[path: "value"].number

                guard let variable = _resolveExistingVar(name: variableName) else {
                    throw Error.undefinedVariable(variableName)
                }

                transaction.suggestValue(variable, value: value)

            case "removeEditVariable":
                let variableName = try change[path: "variable"].string

                guard let variable = _resolveExistingVar(name: variableName) else {
                    throw Error.undefinedVariable(variableName)
                }

                transaction.removeEditVariable(variable)

            case let other:
                throw Error.unknownTransactionOperation(other)
            }
        }
    }

    private static func deserializeConstraint(_ constraint: JSON, _ variableLookup: (String) -> Variable?) throws -> Constraint {
        let op = try constraint[path: "op"].decode(RelationalOperator.self)
        let strength = try constraint[path: "strength"].decode(Double.self)

        let constant = try constraint[path: "expression", "constant"].number
        let terms: [Term] = try constraint[path: "expression", "terms"].array.map {
            let variableName = try $0[path: "variable"].string
            let coefficient = try $0[path: "coefficient"].number

            guard let variable = variableLookup(variableName) else {
                throw Error.undefinedVariable(variableName)
            }

            return Term(variable: variable, coefficient: coefficient)
        }

        let expression = Expression(terms: terms, constant: constant)

        let constraint = Constraint(expr: expression, op: op, strength: strength)

        return constraint
    }

    /// Specifies options for deserializing
    public struct DeserializingOptions {
        /// If `true`, duplicated variables found during deserializing are
        /// collapsed to the same reference, regardless of whether they have
        /// different values.
        public var allowDuplicatedVariables: Bool

        public init(allowDuplicatedVariables: Bool = false) {
            self.allowDuplicatedVariables = allowDuplicatedVariables
        }
    }

    public enum Error: Swift.Error {
        case duplicatedVariableName(_ name: String)
        case undefinedVariable(_ name: String)
        case unknownTransactionOperation(_ name: String)
        case removeConstraintNotFound(Constraint)
    }
}

private func _serialize(solver: Solver) throws -> JSON {
    return [
        "variables": try solver.variables.sorted(by: { $0.name < $1.name }).map(_serialize).json,
        "varEdit": try solver.variableEditInfo.sorted(by: { $0.key.name < $1.key.name }).map(_serialize).json,
        "constraints":
            try solver.constraints.filter {
                !($0 is EditConstraint)
            }.sorted {
                $0.expression.constant < $1.expression.constant
            }.map {
                try _serialize(constraint: $0)
            }.json
    ]
}

private func _serialize(variable: Variable) throws -> JSON {
    return try JSON(fromEncodable: variable)
}

private func _serialize(variable: Variable, varEdit: Solver.EditInfo) throws -> JSON {
    return [
        "variable": variable.name.json,
        "constant": varEdit.constant.json,
        "strength": varEdit.constraint.strength.json
    ]
}

private func _serialize(constraint: Constraint) throws -> JSON {
    return [
        "expression": try _serialize(expression: constraint.expression),
        "op": try JSON(fromEncodable: constraint.op),
        "strength": constraint.strength.json
    ]
}

private func _serialize(expression: Expression) throws -> JSON {
    return [
        "terms": try expression.terms.map(_serialize).json,
        "constant": expression.constant.json
    ]
}

private func _serialize(term: Term) throws -> JSON {
    return [
        "variable": term.variable.name.json,
        "coefficient": term.coefficient.json
    ]
}
