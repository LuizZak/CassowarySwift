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
}

#endif
