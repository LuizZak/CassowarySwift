import XCTest
@testable import CassowarySwift

#if PERFORMANCE_TESTS

class PerformanceTests: XCTestCase {
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

    func testPerformance_transactions_singleTransaction() throws {
        let testFixturePath = fixturesPath
            .appendingPathComponent("PerformanceTestFixture_transactions")
            .appendingPathExtension("json")
        let data = try Data(contentsOf: testFixturePath)

        let transactions = try JSONDecoder().decode([JSON].self, from: data).map { try $0.asData() }

        measureMetrics([.wallClockTime], automaticallyStartMeasuring: false) {
            let solver = Solver()

            do {
                let next = transactions[0]

                let tr = solver.startTransaction()

                try SolverSerializer.deserialize(data: next, transaction: tr)

                startMeasuring()

                try tr.apply()

                stopMeasuring()
            } catch {
                XCTFail("Unexpected error: \(error)")
            }
        }
    }

    func testPerformance_validation_transactions() throws {
        let testFixturePath = fixturesPath
            .appendingPathComponent("ValidationTestFixture_transactions")
            .appendingPathExtension("json")

        let transactionData = try Data(contentsOf: testFixturePath)

        let transactions = try JSONDecoder().decode([JSON].self, from: transactionData).map { try $0.asData() }

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

    func testPerformance_kiwiLike() throws {
        // Test derived from kiwi's benchmark:
        // https://github.com/nucleic/kiwi/blob/ca8e859d95778019a77f2c0c9ffd9a1587b9ccbb/benchmarks/enaml_like_benchmark.cpp

        func setupSolver(_ solver: Solver, width: Variable, height: Variable) throws {
            // Create custom strength
            let mmedium = Strength.create(0.0, 1.0, 0.0, 1.25)
            let smedium = Strength.create(0.0, 100, 0.0)

            // Create the variable
            let left = Variable("left")
            let top = Variable("top")
            let contents_top = Variable("contents_top")
            let contents_bottom = Variable("contents_bottom")
            let contents_left = Variable("contents_left")
            let contents_right = Variable("contents_right")
            let midline = Variable("midline")
            let ctleft = Variable("ctleft")
            let ctheight = Variable("ctheight")
            let cttop = Variable("cttop")
            let ctwidth = Variable("ctwidth")
            let lb1left = Variable("lb1left")
            let lb1height = Variable("lb1height")
            let lb1top = Variable("lb1top")
            let lb1width = Variable("lb1width")
            let lb2left = Variable("lb2left")
            let lb2height = Variable("lb2height")
            let lb2top = Variable("lb2top")
            let lb2width = Variable("lb2width")
            let lb3left = Variable("lb3left")
            let lb3height = Variable("lb3height")
            let lb3top = Variable("lb3top")
            let lb3width = Variable("lb3width")
            let fl1left = Variable("fl1left")
            let fl1height = Variable("fl1height")
            let fl1top = Variable("fl1top")
            let fl1width = Variable("fl1width")
            let fl2left = Variable("fl2left")
            let fl2height = Variable("fl2height")
            let fl2top = Variable("fl2top")
            let fl2width = Variable("fl2width")
            let fl3left = Variable("fl3left")
            let fl3height = Variable("fl3height")
            let fl3top = Variable("fl3top")
            let fl3width = Variable("fl3width")

            // Add the edit variables
            try solver.addEditVariable(variable: width, strength: Strength.STRONG)
            try solver.addEditVariable(variable: height, strength: Strength.STRONG)

            // Add the constraints
            let constraints: [Constraint] = [
                ((left + -0 >= 0) as Constraint).setStrength(Strength.REQUIRED),
                ((height + 0 == 0) as Constraint).setStrength(Strength.MEDIUM),
                ((top + -0 >= 0) as Constraint).setStrength(Strength.REQUIRED),
                ((width + -0 >= 0) as Constraint).setStrength(Strength.REQUIRED),
                ((height + -0 >= 0) as Constraint).setStrength(Strength.REQUIRED),
                ((-top + contents_top + -10 == 0) as Constraint).setStrength(Strength.REQUIRED),
                ((lb3height + -16 == 0) as Constraint).setStrength(Strength.STRONG),
                ((lb3height + -16 >= 0) as Constraint).setStrength(Strength.STRONG),
                ((ctleft + -0 >= 0) as Constraint).setStrength(Strength.REQUIRED),
                ((cttop + -0 >= 0) as Constraint).setStrength(Strength.REQUIRED),
                ((ctwidth + -0 >= 0) as Constraint).setStrength(Strength.REQUIRED),
                ((ctheight + -0 >= 0) as Constraint).setStrength(Strength.REQUIRED),
                ((fl3left + -0 >= 0) as Constraint).setStrength(Strength.REQUIRED),
                ((ctheight + -24 >= 0) as Constraint).setStrength(smedium),
                ((ctwidth + -1.67772e+07 <= 0) as Constraint).setStrength(smedium),
                ((ctheight + -24 <= 0) as Constraint).setStrength(smedium),
                ((fl3top + -0 >= 0) as Constraint).setStrength(Strength.REQUIRED),
                ((fl3width + -0 >= 0) as Constraint).setStrength(Strength.REQUIRED),
                ((fl3height + -0 >= 0) as Constraint).setStrength(Strength.REQUIRED),
                ((lb1width + -67 == 0) as Constraint).setStrength(Strength.WEAK),
                ((lb2width + -0 >= 0) as Constraint).setStrength(Strength.REQUIRED),
                ((lb2height + -0 >= 0) as Constraint).setStrength(Strength.REQUIRED),
                ((fl2height + -0 >= 0) as Constraint).setStrength(Strength.REQUIRED),
                ((lb3left + -0 >= 0) as Constraint).setStrength(Strength.REQUIRED),
                ((fl2width + -125 >= 0) as Constraint).setStrength(Strength.STRONG),
                ((fl2height + -21 == 0) as Constraint).setStrength(Strength.STRONG),
                ((fl2height + -21 >= 0) as Constraint).setStrength(Strength.STRONG),
                ((lb3top + -0 >= 0) as Constraint).setStrength(Strength.REQUIRED),
                ((lb3width + -0 >= 0) as Constraint).setStrength(Strength.REQUIRED),
                ((fl1left + -0 >= 0) as Constraint).setStrength(Strength.REQUIRED),
                ((fl1width + -0 >= 0) as Constraint).setStrength(Strength.REQUIRED),
                ((lb1width + -67 >= 0) as Constraint).setStrength(Strength.STRONG),
                ((fl2left + -0 >= 0) as Constraint).setStrength(Strength.REQUIRED),
                ((lb2width + -66 == 0) as Constraint).setStrength(Strength.WEAK),
                ((lb2width + -66 >= 0) as Constraint).setStrength(Strength.STRONG),
                ((lb2height + -16 == 0) as Constraint).setStrength(Strength.STRONG),
                ((fl1height + -0 >= 0) as Constraint).setStrength(Strength.REQUIRED),
                ((fl1top + -0 >= 0) as Constraint).setStrength(Strength.REQUIRED),
                ((lb2top + -0 >= 0) as Constraint).setStrength(Strength.REQUIRED),
                ((-lb2top + lb3top + -lb2height + -10 == 0) as Constraint).setStrength(mmedium),
                ((-lb3top + -lb3height + fl3top + -10 >= 0) as Constraint).setStrength(Strength.REQUIRED),
                ((-lb3top + -lb3height + fl3top + -10 == 0) as Constraint).setStrength(mmedium),
                ((contents_bottom + -fl3height + -fl3top + -0 == 0) as Constraint).setStrength(mmedium),
                ((fl1top + -contents_top + 0 >= 0) as Constraint).setStrength(Strength.REQUIRED),
                ((fl1top + -contents_top + 0 == 0) as Constraint).setStrength(mmedium),
                ((contents_bottom + -fl3height + -fl3top + -0 >= 0) as Constraint).setStrength(Strength.REQUIRED),
                ((-left + -width + contents_right + 10 == 0) as Constraint).setStrength(Strength.REQUIRED),
                ((-top + -height + contents_bottom + 10 == 0) as Constraint).setStrength(Strength.REQUIRED),
                ((-left + contents_left + -10 == 0) as Constraint).setStrength(Strength.REQUIRED),
                ((lb3left + -contents_left + 0 == 0) as Constraint).setStrength(mmedium),
                ((fl1left + -midline + 0 == 0) as Constraint).setStrength(Strength.STRONG),
                ((fl2left + -midline + 0 == 0) as Constraint).setStrength(Strength.STRONG),
                ((ctleft + -midline + 0 == 0) as Constraint).setStrength(Strength.STRONG),
                ((fl1top + 0.5 * fl1height + -lb1top + -0.5 * lb1height + 0 == 0) as Constraint).setStrength(Strength.STRONG),
                ((lb1left + -contents_left + 0 >= 0) as Constraint).setStrength(Strength.REQUIRED),
                ((lb1left + -contents_left + 0 == 0) as Constraint).setStrength(mmedium),
                ((-lb1left + fl1left + -lb1width + -10 >= 0) as Constraint).setStrength(Strength.REQUIRED),
                ((-lb1left + fl1left + -lb1width + -10 == 0) as Constraint).setStrength(mmedium),
                ((-fl1left + contents_right + -fl1width + -0 >= 0) as Constraint).setStrength(Strength.REQUIRED),
                ((width + 0 == 0) as Constraint).setStrength(Strength.MEDIUM),
                ((-fl1top + fl2top + -fl1height + -10 >= 0) as Constraint).setStrength(Strength.REQUIRED),
                ((-fl1top + fl2top + -fl1height + -10 == 0) as Constraint).setStrength(mmedium),
                ((cttop + -fl2top + -fl2height + -10 >= 0) as Constraint).setStrength(Strength.REQUIRED),
                ((-ctheight + -cttop + fl3top + -10 >= 0) as Constraint).setStrength(Strength.REQUIRED),
                ((contents_bottom + -fl3height + -fl3top + -0 >= 0) as Constraint).setStrength(Strength.REQUIRED),
                ((cttop + -fl2top + -fl2height + -10 == 0) as Constraint).setStrength(mmedium),
                ((-fl1left + contents_right + -fl1width + -0 == 0) as Constraint).setStrength(mmedium),
                ((-lb2top + -0.5 * lb2height + fl2top + 0.5 * fl2height + 0 == 0) as Constraint).setStrength(Strength.STRONG),
                ((-contents_left + lb2left + 0 >= 0) as Constraint).setStrength(Strength.REQUIRED),
                ((-contents_left + lb2left + 0 == 0) as Constraint).setStrength(mmedium),
                ((fl2left + -lb2width + -lb2left + -10 >= 0) as Constraint).setStrength(Strength.REQUIRED),
                ((-ctheight + -cttop + fl3top + -10 == 0) as Constraint).setStrength(mmedium),
                ((contents_bottom + -fl3height + -fl3top + -0 == 0) as Constraint).setStrength(mmedium),
                ((lb1top + -0 >= 0) as Constraint).setStrength(Strength.REQUIRED),
                ((lb1width + -0 >= 0) as Constraint).setStrength(Strength.REQUIRED),
                ((lb1height + -0 >= 0) as Constraint).setStrength(Strength.REQUIRED),
                ((fl2left + -lb2width + -lb2left + -10 == 0) as Constraint).setStrength(mmedium),
                ((-fl2left + -fl2width + contents_right + -0 == 0) as Constraint).setStrength(mmedium),
                ((-fl2left + -fl2width + contents_right + -0 >= 0) as Constraint).setStrength(Strength.REQUIRED),
                ((lb3left + -contents_left + 0 >= 0) as Constraint).setStrength(Strength.REQUIRED),
                ((lb1left + -0 >= 0) as Constraint).setStrength(Strength.REQUIRED),
                ((0.5 * ctheight + cttop + -lb3top + -0.5 * lb3height + 0 == 0) as Constraint).setStrength(Strength.STRONG),
                ((ctleft + -lb3left + -lb3width + -10 >= 0) as Constraint).setStrength(Strength.REQUIRED),
                ((-ctwidth + -ctleft + contents_right + -0 >= 0) as Constraint).setStrength(Strength.REQUIRED),
                ((ctleft + -lb3left + -lb3width + -10 == 0) as Constraint).setStrength(mmedium),
                ((fl3left + -contents_left + 0 >= 0) as Constraint).setStrength(Strength.REQUIRED),
                ((fl3left + -contents_left + 0 == 0) as Constraint).setStrength(mmedium),
                ((-ctwidth + -ctleft + contents_right + -0 == 0) as Constraint).setStrength(mmedium),
                ((-fl3left + contents_right + -fl3width + -0 == 0) as Constraint).setStrength(mmedium),
                ((-contents_top + lb1top + 0 >= 0) as Constraint).setStrength(Strength.REQUIRED),
                ((-contents_top + lb1top + 0 == 0) as Constraint).setStrength(mmedium),
                ((-fl3left + contents_right + -fl3width + -0 >= 0) as Constraint).setStrength(Strength.REQUIRED),
                ((lb2top + -lb1top + -lb1height + -10 >= 0) as Constraint).setStrength(Strength.REQUIRED),
                ((-lb2top + lb3top + -lb2height + -10 >= 0) as Constraint).setStrength(Strength.REQUIRED),
                ((lb2top + -lb1top + -lb1height + -10 == 0) as Constraint).setStrength(mmedium),
                ((fl1height + -21 == 0) as Constraint).setStrength(Strength.STRONG),
                ((fl1height + -21 >= 0) as Constraint).setStrength(Strength.STRONG),
                ((lb2left + -0 >= 0) as Constraint).setStrength(Strength.REQUIRED),
                ((lb2height + -16 >= 0) as Constraint).setStrength(Strength.STRONG),
                ((fl2top + -0 >= 0) as Constraint).setStrength(Strength.REQUIRED),
                ((fl2width + -0 >= 0) as Constraint).setStrength(Strength.REQUIRED),
                ((lb1height + -16 >= 0) as Constraint).setStrength(Strength.STRONG),
                ((lb1height + -16 == 0) as Constraint).setStrength(Strength.STRONG),
                ((fl3width + -125 >= 0) as Constraint).setStrength(Strength.STRONG),
                ((fl3height + -21 == 0) as Constraint).setStrength(Strength.STRONG),
                ((fl3height + -21 >= 0) as Constraint).setStrength(Strength.STRONG),
                ((lb3height + -0 >= 0) as Constraint).setStrength(Strength.REQUIRED),
                ((ctwidth + -119 >= 0) as Constraint).setStrength(smedium),
                ((lb3width + -24 == 0) as Constraint).setStrength(Strength.WEAK),
                ((lb3width + -24 >= 0) as Constraint).setStrength(Strength.STRONG),
                ((fl1width + -125 >= 0) as Constraint).setStrength(Strength.STRONG),
            ]

            for constraint in constraints {
                try solver.addConstraint(constraint)
            }
        }

        struct Size {
            var width: Double
            var height: Double
        }

        let sizes: [Size] = [
            Size(width: 400, height: 600),
            Size(width: 600, height: 400),
            Size(width: 800, height: 1200),
            Size(width: 1200, height: 800),
            Size(width: 400, height: 800),
            Size(width: 800, height: 400)
        ]

        measure {
            do {
                let solver = Solver()

                let width = Variable("width")
                let height = Variable("height")

                try setupSolver(solver, width: width, height: height)

                for size in sizes {
                    try solver.suggestValue(variable: width, value: size.width)
                    try solver.suggestValue(variable: height, value: size.height)
                }
            } catch {
                XCTFail("Unexpected error: \(error)")
            }
        }
    }
}

#endif // PERFORMANCE_TESTS
