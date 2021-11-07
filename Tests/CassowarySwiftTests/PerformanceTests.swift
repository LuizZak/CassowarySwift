import XCTest
@testable import CassowarySwift

#if PERFORMANCE_TESTS

class PerformanceTests: XCTestCase {
    var fixturesPath: URL {
        URL(fileURLWithPath: #filePath)
            .deletingLastPathComponent()
            .deletingLastPathComponent()
            .appendingPathComponent("Fixtures")
    }

    override func setUpWithError() throws {
        try super.setUpWithError()

        self.continueAfterFailure = true
    }

    func testPerformance() throws {
        let testFixturePath = fixturesPath
            .appendingPathComponent("PerformanceTestFixture")
            .appendingPathExtension("json")
        let data = try Data(contentsOf: testFixturePath)

        measure {
            do {
                _=try SolverSerializer.deserialize(
                    data: data,
                    options: .init(allowDuplicatedVariables: true)
                )
            } catch {
                XCTFail("Unexpected error: \(error)")
            }
        }
    }

    func testPerformance_transactions() throws {
        let testFixturePath = fixturesPath
            .appendingPathComponent("PerformanceTestFixture_transactions")
            .appendingPathExtension("json")
        let data = try Data(contentsOf: testFixturePath)

        let transactions = try JSONDecoder().decode([JSON].self, from: data).map { try $0.asData() }

        measure {
            let solver = Solver()

            do {
                for next in transactions {
                    let tr = solver.startTransaction()
                    try SolverSerializer.deserialize(data: next, transaction: tr)
                    try tr.apply()
                }
            } catch {
                XCTFail("Unexpected error: \(error)")
            }
        }
    }

    func testPerformance_transactions_validating() throws {
        self.continueAfterFailure = false

        let testFixturePath = fixturesPath
            .appendingPathComponent("ValidationTestFixture_transactions")
            .appendingPathExtension("json")
        let variablesFixturePath = fixturesPath
            .appendingPathComponent("ValidationTestFixture_variables")
            .appendingPathExtension("json")

        let transactionData = try Data(contentsOf: testFixturePath)
        let variablesPath = try Data(contentsOf: variablesFixturePath)

        let transactions = try JSONDecoder().decode([JSON].self, from: transactionData).map { try $0.asData() }
        let variables = try JSONDecoder().decode([[JSON]].self, from: variablesPath)

        measure {
            let solver = Solver()

            do {
                for (i, next) in transactions.enumerated() {
                    let variablesToCheck = variables[i]

                    let tr = solver.startTransaction()

                    try SolverSerializer.deserialize(data: next, transaction: tr)
                    try tr.apply()

                    let varDict = Dictionary(solver.variables.map { ($0.name, $0) }) { $1 }

                    for v in variablesToCheck {
                        let varName = try v[path: "name"].string
                        let expectedValue = try v[path: "value"].number

                        guard let solverVar = varDict[varName] else {
                            continue
                        }

                        if solverVar.value != expectedValue {
                            XCTFail("Expected variable \(varName) to have value of \(expectedValue) after transaction #\(i + 1), but found \(solverVar.value)")
                            return
                        }
                    }
                }
            } catch {
                XCTFail("Unexpected error: \(error)")
            }
        }
    }
}

#endif // PERFORMANCE_TESTS
