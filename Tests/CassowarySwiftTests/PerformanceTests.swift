import XCTest
@testable import CassowarySwift

#if PERFORMANCE_TESTS

class PerformanceTests: XCTestCase {
    func testPerformance() throws {
        let testFixturePath = URL(fileURLWithPath: #filePath)
            .deletingLastPathComponent()
            .deletingLastPathComponent()
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
        let testFixturePath = URL(fileURLWithPath: #filePath)
            .deletingLastPathComponent()
            .deletingLastPathComponent()
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
}

#endif // PERFORMANCE_TESTS
