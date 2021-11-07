import XCTest
@testable import CassowarySwift

class SolverSerializerTests: XCTestCase {
    func testSerialize() throws {
        let expected: JSON = [
            "constraints": [
                [
                    "expression": [
                        "constant": -200.0,
                        "terms": [
                            [
                                "coefficient": 1.0,
                                "variable": "v2"
                            ]
                        ]
                    ],
                    "op": "lessThanOrEqual",
                    "strength": 1001001000.0
                ],
                [
                    "expression": [
                        "constant": -10.0,
                        "terms": [
                            [
                                "coefficient": 1.0,
                                "variable": "v1"
                            ]
                        ]
                    ],
                    "op": "greaterThanOrEqual",
                    "strength": 1001001000.0
                ],
                [
                    "expression": [
                        "constant": 0.0,
                        "terms": [
                            [
                                "coefficient": 0.5,
                                "variable": "v1"
                            ],
                            [
                                "coefficient": 0.5,
                                "variable": "v2"
                            ],
                            [
                                "coefficient": -1.0,
                                "variable": "v3"
                            ]
                        ]
                    ],
                    "op": "equal",
                    "strength": 1001001000.0
                ],
                [
                    "expression": [
                        "constant": 30.0,
                        "terms": [
                            [
                                "coefficient": 1.0,
                                "variable": "v1"
                            ],
                            [
                                "coefficient": -1.0,
                                "variable": "v2"
                            ]
                        ]
                    ],
                    "op": "equal",
                    "strength": 1001001000.0
                ]
            ],
            "varEdit": [
                [
                    "constant": 60.0,
                    "strength": 1000000.0,
                    "variable": "v3"
                ]
            ],
            "variables": [
                [
                    "name": "v1",
                    "value": 45.0
                ],
                [
                    "name": "v2",
                    "value": 75.0
                ],
                [
                    "name": "v3",
                    "value": 60.0
                ]
            ]
        ]
        let solver = Solver()
        try solver.withTransaction {
            let v1 = Variable("v1")
            let v2 = Variable("v2")
            let v3 = Variable("v3")

            $0.addConstraint(v1 >= 10)
            $0.addConstraint(v2 <= 200)
            $0.addConstraint(v2 == v1 + 30)
            $0.addConstraint(v3 == (v1 + v2) / 2)
            $0.addEditVariable(v3, strength: Strength.STRONG)
            $0.suggestValue(v3, value: 60)
        }
        let data = try SolverSerializer.serialize(solver: solver)
        let json = try JSON(data: data)

        XCTAssertEqual(expected, json)
    }

    func testDeserialize() throws {
        let json: JSON = [
            "constraints": [
                [
                    "expression": [
                        "constant": -200.0,
                        "terms": [
                            [
                                "coefficient": 1.0,
                                "variable": "v2"
                            ]
                        ]
                    ],
                    "op": "lessThanOrEqual",
                    "strength": 1001001000.0
                ],
                [
                    "expression": [
                        "constant": -10.0,
                        "terms": [
                            [
                                "coefficient": 1.0,
                                "variable": "v1"
                            ]
                        ]
                    ],
                    "op": "greaterThanOrEqual",
                    "strength": 1001001000.0
                ],
                [
                    "expression": [
                        "constant": 0.0,
                        "terms": [
                            [
                                "coefficient": 0.5,
                                "variable": "v1"
                            ],
                            [
                                "coefficient": -1.0,
                                "variable": "v3"
                            ],
                            [
                                "coefficient": 0.5,
                                "variable": "v2"
                            ]
                        ]
                    ],
                    "op": "equal",
                    "strength": 1001001000.0
                ],
                [
                    "expression": [
                        "constant": 30.0,
                        "terms": [
                            [
                                "coefficient": 1.0,
                                "variable": "v1"
                            ],
                            [
                                "coefficient": -1.0,
                                "variable": "v2"
                            ]
                        ]
                    ],
                    "op": "equal",
                    "strength": 1001001000.0
                ]
            ],
            "varEdit": [
                [
                    "constant": 60.0,
                    "strength": 1000000.0,
                    "variable": "v3"
                ]
            ],
            "variables": [
                [
                    "name": "v1",
                    "value": 45.0
                ],
                [
                    "name": "v2",
                    "value": 75.0
                ],
                [
                    "name": "v3",
                    "value": 60.0
                ]
            ]
        ]
        let (solver, variables) = try SolverSerializer.deserialize(data: json.asData())

        solver.updateVariables()

        XCTAssertEqual(variables[0].name, "v1")
        XCTAssertEqual(variables[0].value, 45.0)
        XCTAssertEqual(variables[1].name, "v2")
        XCTAssertEqual(variables[1].value, 75.0)
        XCTAssertEqual(variables[2].name, "v3")
        XCTAssertEqual(variables[2].value, 60.0)
    }

    func testDeserialize_allowDuplicatedVariables() throws {
        let json: JSON = [
            "constraints": [],
            "varEdit": [],
            "variables": [
                [
                    "name": "v1",
                    "value": 45.0
                ],
                [
                    "name": "v1",
                    "value": 50.0
                ],
            ]
        ]

        let (_, variables) =
        try SolverSerializer.deserialize(
            data: json.asData(),
            options: .init(allowDuplicatedVariables: true)
        )

        XCTAssertEqual(variables.count, 1)
        XCTAssertEqual(variables[0].name, "v1")
    }

    func testDeserialize_reduceExpressions_true() throws {
        let json: JSON = [
            "constraints": [
                [
                    "expression": [
                        "constant": 0.0,
                        "terms": [
                            [
                                "coefficient": 1.0,
                                "variable": "v1"
                            ],
                            [
                                "coefficient": -1.0,
                                "variable": "v3"
                            ],
                            [
                                "coefficient": 0.5,
                                "variable": "v2"
                            ],
                            [
                                "coefficient": -0.5,
                                "variable": "v1"
                            ]
                        ]
                    ],
                    "op": "equal",
                    "strength": 1001001000.0
                ]
            ],
            "varEdit": [],
            "variables": [
                [
                    "name": "v1",
                    "value": 45.0
                ],
                [
                    "name": "v2",
                    "value": 75.0
                ],
                [
                    "name": "v3",
                    "value": 60.0
                ]
            ]
        ]
        let (solver, _) = try SolverSerializer.deserialize(data: json.asData(), options: .init(reduceExpressions: true))

        XCTAssertEqual(solver.constraints.count, 1)
        let expression = solver.constraints[0].expression
        XCTAssertEqual(expression.terms.count, 3)
        XCTAssertEqual(expression.terms[0].variable.name, "v1")
        XCTAssertEqual(expression.terms[0].coefficient, 0.5)
        XCTAssertEqual(expression.terms[1].variable.name, "v3")
        XCTAssertEqual(expression.terms[1].coefficient, -1.0)
        XCTAssertEqual(expression.terms[2].variable.name, "v2")
        XCTAssertEqual(expression.terms[2].coefficient, 0.5)
    }

    func testDeserialize_reduceExpressions_false() throws {
        let json: JSON = [
            "constraints": [
                [
                    "expression": [
                        "constant": 0.0,
                        "terms": [
                            [
                                "coefficient": 1.0,
                                "variable": "v1"
                            ],
                            [
                                "coefficient": -1.0,
                                "variable": "v3"
                            ],
                            [
                                "coefficient": 0.5,
                                "variable": "v2"
                            ],
                            [
                                "coefficient": -0.5,
                                "variable": "v1"
                            ]
                        ]
                    ],
                    "op": "equal",
                    "strength": 1001001000.0
                ]
            ],
            "varEdit": [],
            "variables": [
                [
                    "name": "v1",
                    "value": 45.0
                ],
                [
                    "name": "v2",
                    "value": 75.0
                ],
                [
                    "name": "v3",
                    "value": 60.0
                ]
            ]
        ]
        let (solver, _) = try SolverSerializer.deserialize(data: json.asData(), options: .init(reduceExpressions: false))

        XCTAssertEqual(solver.constraints.count, 1)
        let expression = solver.constraints[0].expression
        XCTAssertEqual(expression.terms.count, 4)
        XCTAssertEqual(expression.terms[0].variable.name, "v1")
        XCTAssertEqual(expression.terms[0].coefficient, 1.0)
        XCTAssertEqual(expression.terms[1].variable.name, "v3")
        XCTAssertEqual(expression.terms[1].coefficient, -1.0)
        XCTAssertEqual(expression.terms[2].variable.name, "v2")
        XCTAssertEqual(expression.terms[2].coefficient, 0.5)
        XCTAssertEqual(expression.terms[3].variable.name, "v1")
        XCTAssertEqual(expression.terms[3].coefficient, -0.5)
    }

    func testDeserialize_allowDuplicatedVariables_avoidDoubleEdit() throws {
        let json: JSON = [
            "constraints": [],
            "varEdit": [
                [
                    "variable": "v1",
                    "constant": 1.0,
                    "strength": 1.0
                ],
                [
                    "variable": "v1",
                    "constant": 2.0,
                    "strength": 2.0
                ]
            ],
            "variables": [
                [
                    "name": "v1",
                    "value": 45.0
                ],
                [
                    "name": "v1",
                    "value": 50.0
                ],
            ]
        ]

        let (_, variables) =
        try SolverSerializer.deserialize(
            data: json.asData(),
            options: .init(allowDuplicatedVariables: true)
        )

        XCTAssertEqual(variables.count, 1)
        XCTAssertEqual(variables[0].name, "v1")
    }

    func testDeserialize_failsOnDuplicatedVariableNames() throws {
        let json: JSON = [
            "constraints": [],
            "varEdit": [],
            "variables": [
                [
                    "name": "v1",
                    "value": 45.0
                ],
                [
                    "name": "v1",
                    "value": 50.0
                ],
            ]
        ]

        do {
            _=try SolverSerializer.deserialize(data: json.asData())
            XCTFail("Expected duplicate variable error.")
        } catch SolverSerializer.Error.duplicatedVariableName("v1") {
            // Success
        } catch {
            XCTFail("Unexpected error: \(error)")
        }
    }

    func testSerializeTransaction_addConstraint() throws {
        let expected: JSON = [
            [
                "change": "addConstraint",
                "constraint": [
                    "expression": [
                        "constant": 0.0,
                        "terms": [
                            [
                                "coefficient": 1.0,
                                "variable": "v1"
                            ],
                            [
                                "coefficient": -1.0,
                                "variable": "v2"
                            ]
                        ]
                    ],
                    "op": "equal",
                    "strength": 1001001000.0
                ]
            ]
        ]
        let solver = Solver()
        let v1 = Variable("v1")
        let v2 = Variable("v2")
        let tr = solver.startTransaction()
        tr.addConstraint(v1 == v2)

        let data = try SolverSerializer.serialize(transaction: tr)

        let json = try JSON(data: data)
        XCTAssertEqual(expected, json, json.swiftDescription)
    }

    func testSerializeTransaction_removeConstraint() throws {
        let expected: JSON = [
            [
                "change": "removeConstraint",
                "constraint": [
                    "expression": [
                        "constant": 0.0,
                        "terms": [
                            [
                                "coefficient": 1.0,
                                "variable": "v1"
                            ],
                            [
                                "coefficient": -1.0,
                                "variable": "v2"
                            ]
                        ]
                    ],
                    "op": "equal",
                    "strength": 1001001000.0
                ]
            ]
        ]
        let solver = Solver()
        let v1 = Variable("v1")
        let v2 = Variable("v2")
        let tr = solver.startTransaction()
        tr.removeConstraint(v1 == v2)

        let data = try SolverSerializer.serialize(transaction: tr)

        let json = try JSON(data: data)
        XCTAssertEqual(expected, json, json.swiftDescription)
    }

    func testSerializeTransaction_addEditVariable() throws {
        let expected: JSON = [
            [
                "change": "addEditVariable",
                "variable": "v1",
                "strength": 1234.0
            ]
        ]
        let solver = Solver()
        let v1 = Variable("v1")
        let tr = solver.startTransaction()
        tr.addEditVariable(v1, strength: 1234.0)

        let data = try SolverSerializer.serialize(transaction: tr)

        let json = try JSON(data: data)
        XCTAssertEqual(expected, json, json.swiftDescription)
    }

    func testSerializeTransaction_suggestValue() throws {
        let expected: JSON = [
            [
                "change": "suggestValue",
                "variable": "v1",
                "value": 1234.0
            ]
        ]
        let solver = Solver()
        let v1 = Variable("v1")
        let tr = solver.startTransaction()
        tr.suggestValue(v1, value: 1234.0)

        let data = try SolverSerializer.serialize(transaction: tr)

        let json = try JSON(data: data)
        XCTAssertEqual(expected, json, json.swiftDescription)
    }

    func testSerializeTransaction_removeEditVariable() throws {
        let expected: JSON = [
            [
                "change": "removeEditVariable",
                "variable": "v1"
            ]
        ]
        let solver = Solver()
        let v1 = Variable("v1")
        let tr = solver.startTransaction()
        tr.removeEditVariable(v1)

        let data = try SolverSerializer.serialize(transaction: tr)

        let json = try JSON(data: data)
        XCTAssertEqual(expected, json, json.swiftDescription)
    }

    func testDeserializeTransaction_addConstraint() throws {
        let json: JSON = [
            [
                "change": "addConstraint",
                "constraint": [
                    "expression": [
                        "constant": 0.0,
                        "terms": [
                            [
                                "coefficient": 1.0,
                                "variable": "v1"
                            ],
                            [
                                "coefficient": -1.0,
                                "variable": "v2"
                            ]
                        ]
                    ],
                    "op": "equal",
                    "strength": 1001001000.0
                ]
            ]
        ]
        let solver = Solver()
        let tr = solver.startTransaction()

        try SolverSerializer.deserialize(data: json.asData(), transaction: tr)

        XCTAssertEqual(tr.changes.count, 1)
        switch tr.changes[0] {
        case .addConstraint(let c) where c.isEquivalent(to: Variable("v1") == Variable("v2")):
            break
        default:
            XCTFail("Unexpected change array: \(tr.changes)")
        }
    }

    func testDeserializeTransaction_removeConstraint() throws {
        let json: JSON = [
            [
                "change": "removeConstraint",
                "constraint": [
                    "expression": [
                        "constant": 0.0,
                        "terms": [
                            [
                                "coefficient": 1.0,
                                "variable": "v1"
                            ],
                            [
                                "coefficient": -1.0,
                                "variable": "v2"
                            ]
                        ]
                    ],
                    "op": "equal",
                    "strength": 1001001000.0
                ]
            ]
        ]
        let solver = Solver()
        try solver.addConstraint(Variable("v1") == Variable("v2"))
        let tr = solver.startTransaction()

        try SolverSerializer.deserialize(data: json.asData(), transaction: tr)

        XCTAssertEqual(tr.changes.count, 1)
        switch tr.changes[0] {
        case .removeConstraint(let c) where c.isEquivalent(to: Variable("v1") == Variable("v2")):
            break
        default:
            XCTFail("Unexpected change array: \(tr.changes)")
        }
    }

    func testDeserializeTransaction_removeConstraint_throwsErrorIfConstraintNotFound() throws {
        let json: JSON = [
            [
                "change": "removeConstraint",
                "constraint": [
                    "expression": [
                        "constant": 0.0,
                        "terms": [
                            [
                                "coefficient": 1.0,
                                "variable": "v1"
                            ],
                            [
                                "coefficient": -1.0,
                                "variable": "v2"
                            ]
                        ]
                    ],
                    "op": "equal",
                    "strength": 1001001000.0
                ]
            ]
        ]
        let solver = Solver()
        let tr = solver.startTransaction()

        do {
            try SolverSerializer.deserialize(data: json.asData(), transaction: tr)
            XCTFail("Expected to fail")
        } catch SolverSerializer.Error.removeConstraintNotFound(let c) {
            let expected: Constraint = Variable("v1") == Variable("v2")
            XCTAssertTrue(c.isEquivalent(to: expected), "\(c) != \(expected)")
        } catch {
            XCTFail("Unexpected error: \(error)")
        }
    }

    func testDeserializeTransaction_addEditVariable() throws {
        let json: JSON = [
            [
                "change": "addEditVariable",
                "variable": "v1",
                "strength": 1234.0
            ]
        ]
        let solver = Solver()
        let tr = solver.startTransaction()

        try SolverSerializer.deserialize(data: json.asData(), transaction: tr)

        XCTAssertEqual(tr.changes.count, 1)
        switch tr.changes[0] {
        case .addEditVariable(let v, let s) where v.name == "v1" && s == 1234.0:
            break
        default:
            XCTFail("Unexpected change array: \(tr.changes)")
        }
    }

    func testDeserializeTransaction_addEditVariable_reusesExistingVariableIfPresent() throws {
        let json: JSON = [
            [
                "change": "addEditVariable",
                "variable": "v1",
                "strength": 1234.0
            ]
        ]
        let solver = Solver()
        let v1 = Variable("v1")
        try solver.addConstraint(v1 >= 0)
        let tr = solver.startTransaction()

        try SolverSerializer.deserialize(data: json.asData(), transaction: tr)

        XCTAssertEqual(tr.changes.count, 1)
        switch tr.changes[0] {
        case .addEditVariable(let v, let s) where v.name == "v1" && s == 1234.0:
            XCTAssertEqual(solver.variables.count, 1)
            XCTAssertIdentical(v, v1, "Expected variable in solver to be reused")
        default:
            XCTFail("Unexpected change array: \(tr.changes)")
        }
    }

    func testDeserializeTransaction_suggestValue() throws {
        let json: JSON = [
            [
                "change": "suggestValue",
                "variable": "v1",
                "value": 1234.0
            ]
        ]
        let solver = Solver()
        try solver.addConstraint(Variable("v1") >= 0)
        let tr = solver.startTransaction()

        try SolverSerializer.deserialize(data: json.asData(), transaction: tr)

        XCTAssertEqual(tr.changes.count, 1)
        switch tr.changes[0] {
        case .suggestValue(let v, let val) where v.name == "v1" && val == 1234.0:
            break
        default:
            XCTFail("Unexpected change array: \(tr.changes)")
        }
    }

    func testDeserializeTransaction_suggestValue_throwsErrorOnUnknownVariable() throws {
        let json: JSON = [
            [
                "change": "suggestValue",
                "variable": "v1",
                "value": 1234.0
            ]
        ]
        let solver = Solver()
        let tr = solver.startTransaction()

        do {
            try SolverSerializer.deserialize(data: json.asData(), transaction: tr)
            XCTFail("Expected to fail")
        } catch SolverSerializer.Error.undefinedVariable("v1") {
            // Success
        } catch {
            XCTFail("Unexpected error: \(error)")
        }
    }

    func testDeserializeTransaction_suggestValue_reusesRecentlyCreatedVariables() throws {
        let json: JSON = [
            [
                "change": "addEditVariable",
                "variable": "v1",
                "strength": 1.0
            ],
            [
                "change": "suggestValue",
                "variable": "v1",
                "value": 1234.0
            ]
        ]
        let solver = Solver()
        let tr = solver.startTransaction()

        try SolverSerializer.deserialize(data: json.asData(), transaction: tr)

        XCTAssertEqual(tr.changes.count, 2)

        let var1: Variable
        // addEditVariable
        switch tr.changes[0] {
        case .addEditVariable(let v, let val) where v.name == "v1" && val == 1.0:
            var1 = v

        default:
            XCTFail("Unexpected change array: \(tr.changes)")
            return
        }
        // suggestValue
        switch tr.changes[1] {
        case .suggestValue(let v, let val) where v.name == "v1" && val == 1234.0:
            XCTAssertIdentical(v, var1, "Expected variable in recent transaction deserializing to be reused")
        default:
            XCTFail("Unexpected change array: \(tr.changes)")
        }
    }

    func testDeserializeTransaction_removeEditVariable() throws {
        let json: JSON = [
            [
                "change": "removeEditVariable",
                "variable": "v1",
                "value": 1234.0
            ]
        ]
        let solver = Solver()
        try solver.addConstraint(Variable("v1") >= 0)
        let tr = solver.startTransaction()

        try SolverSerializer.deserialize(data: json.asData(), transaction: tr)

        XCTAssertEqual(tr.changes.count, 1)
        switch tr.changes[0] {
        case .removeEditVariable(let v) where v.name == "v1":
            break
        default:
            XCTFail("Unexpected change array: \(tr.changes)")
        }
    }

    func testDeserializeTransaction_removeEditVariable_throwsErrorOnUnknownVariable() throws {
        let json: JSON = [
            [
                "change": "removeEditVariable",
                "variable": "v1"
            ]
        ]
        let solver = Solver()
        let tr = solver.startTransaction()

        do {
            try SolverSerializer.deserialize(data: json.asData(), transaction: tr)
            XCTFail("Expected to fail")
        } catch SolverSerializer.Error.undefinedVariable("v1") {
            // Success
        } catch {
            XCTFail("Unexpected error: \(error)")
        }
    }

    func testDeserializeTransaction_removeEditVariable_reusesRecentlyCreatedVariables() throws {
        let json: JSON = [
            [
                "change": "addEditVariable",
                "variable": "v1",
                "strength": 1.0
            ],
            [
                "change": "removeEditVariable",
                "variable": "v1"
            ]
        ]
        let solver = Solver()
        let tr = solver.startTransaction()

        try SolverSerializer.deserialize(data: json.asData(), transaction: tr)

        XCTAssertEqual(tr.changes.count, 2)

        let var1: Variable
        // addEditVariable
        switch tr.changes[0] {
        case .addEditVariable(let v, let val) where v.name == "v1" && val == 1.0:
            var1 = v

        default:
            XCTFail("Unexpected change array: \(tr.changes)")
            return
        }
        // removeEditVariable
        switch tr.changes[1] {
        case .removeEditVariable(let v) where v.name == "v1":
            XCTAssertIdentical(v, var1, "Expected variable in recent transaction deserializing to be reused")
        default:
            XCTFail("Unexpected change array: \(tr.changes)")
        }
    }
}
