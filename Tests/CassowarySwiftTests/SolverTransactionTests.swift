import XCTest
import CassowarySwift

class SolverTransactionTests: XCTestCase {
    func testEphemeral() throws {
        let solver = Solver()
        let tr = solver.startTransaction()

        XCTAssertFalse(tr.isCancelled)
    }

    func testCancel_stopsTransaction() throws {
        let solver = Solver()
        let x = Variable("x")
        let tr = solver.startTransaction()

        tr.addConstraint(x + 2 == 20)

        tr.cancel()

        try tr.apply()

        XCTAssertTrue(tr.isCancelled)
        solver.updateVariables()
        assertIsCloseTo(x, 0)
    }
}
