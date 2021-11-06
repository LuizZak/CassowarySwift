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
            $0.addEditVariable(variable: v3, strength: Strength.STRONG)
            $0.suggestValue(variable: v3, value: 60)
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
}
