import XCTest
@testable import CassowarySwift

class ValidationTests: XCTestCase {
    func testSolver_validation() throws {
        self.continueAfterFailure = false

        let testFixturePath = fixturesPath
            .appendingPathComponent("ValidationTestFixture_transactions")
            .appendingPathExtension("json")

        let transactionData = try Data(contentsOf: testFixturePath)
        let transactions = try JSONDecoder().decode([JSON].self, from: transactionData).map { try $0.asData() }

        let variablesFixturePath = fixturesPath
            .appendingPathComponent("ValidationTestFixture_variables")
            .appendingPathExtension("json")

        let variablesPath = try Data(contentsOf: variablesFixturePath)
        let variables = try JSONDecoder().decode([[JSON]].self, from: variablesPath)

        let solver = Solver()

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
    }
}
