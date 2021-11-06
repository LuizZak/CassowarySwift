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
    public static func deserialize(data: Data, options: DeserializationOptions = .init()) throws -> (Solver, [Variable]) {
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

        let variables = variablesDict.values.sorted { $0.name < $1.name }

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

            transaction.addEditVariable(variable: variable, strength: strength)
            transaction.suggestValue(variable: variable, value: constant)
        }

        // Extract constraints
        for constraint in try json[path: "constraints"].array {
            let op = try constraint[path: "op"].decode(RelationalOperator.self)
            let strength = try constraint[path: "strength"].decode(Double.self)

            let constant = try constraint[path: "expression", "constant"].number
            let terms: [Term] = try constraint[path: "expression", "terms"].array.map {
                let variableName = try $0[path: "variable"].string
                let coefficient = try $0[path: "coefficient"].number

                guard let variable = variablesDict[variableName] else {
                    throw Error.undefinedVariable(variableName)
                }

                return Term(variable: variable, coefficient: coefficient)
            }

            let expression = Expression(terms: terms, constant: constant)

            let constraint = Constraint(expr: expression, op: op, strength: strength)

            transaction.addConstraint(constraint)
        }

        try transaction.apply()

        solver.updateVariables()

        return (solver, variables)
    }

    /// Specifies options for deserialization
    public struct DeserializationOptions {
        /// If `true`, duplicated variables found during deserialization are
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
        "terms": try expression.terms.sorted(by: { $0.variable.name < $1.variable.name }).map(_serialize).json,
        "constant": expression.constant.json
    ]
}

private func _serialize(term: Term) throws -> JSON {
    return [
        "variable": term.variable.name.json,
        "coefficient": term.coefficient.json
    ]
}
