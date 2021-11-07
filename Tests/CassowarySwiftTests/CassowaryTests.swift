/*

 Copyright (c) 2017, Tribal Worldwide London
 Copyright (c) 2015, Alex Birkett
 All rights reserved.

 Redistribution and use in source and binary forms, with or without
 modification, are permitted provided that the following conditions are met:

 * Redistributions of source code must retain the above copyright notice, this
 list of conditions and the following disclaimer.

 * Redistributions in binary form must reproduce the above copyright notice,
 this list of conditions and the following disclaimer in the documentation
 and/or other materials provided with the distribution.

 * Neither the name of kiwi-java nor the names of its
 contributors may be used to endorse or promote products derived from
 this software without specific prior written permission.

 THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
 FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
 CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
 OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

 */

import XCTest
@testable import CassowarySwift

class CassowaryTests: XCTestCase {

    func testSimple() throws {
        let solver = Solver()
        let x = Variable("x")
        let tr = solver.startTransaction()

        tr.addConstraint(x + 2 == 20)

        try tr.apply()

        solver.updateVariables()
        assertIsCloseTo(x, 18)
    }

    func testSimple0() throws {
        let solver = Solver()
        let x = Variable("x")
        let y = Variable("y")
        let tr = solver.startTransaction()

        tr.addConstraint(x == 20)
        tr.addConstraint(x + 2 == y + 10)

        try tr.apply()

        solver.updateVariables()

        assertIsCloseTo(x, 20)
        assertIsCloseTo(y, 12)
    }

    func testSimple1() throws {
        let solver = Solver()
        let x = Variable("x")
        let y = Variable("y")
        let tr = solver.startTransaction()

        tr.addConstraint(x == y)

        try tr.apply()

        solver.updateVariables()

        assertIsCloseTo(x, y)
    }

    func testCasso1() throws {
        let solver = Solver()
        let x = Variable("x")
        let y = Variable("y")
        let tr = solver.startTransaction()

        tr.addConstraint(x <= y)
        tr.addConstraint(y == x + 3.0)
        tr.addConstraint((x == 10.0).setStrength(Strength.WEAK))
        tr.addConstraint((y == 10.0).setStrength(Strength.WEAK))

        try tr.apply()

        solver.updateVariables()

        if abs(x.value - 10.0) < Double.epsilon {
            assertIsCloseTo(10.0, x)
            assertIsCloseTo(13.0, y)
        } else {
            assertIsCloseTo(7.0, x)
            assertIsCloseTo(10.0, y)
        }
    }

    func testAddDelete1() throws {
        let solver = Solver()
        let x = Variable("x")

        try solver.withTransaction {
            $0.addConstraint((x <= 100).setStrength(Strength.WEAK))
        }

        solver.updateVariables()

        assertIsCloseTo(100, x)

        let c10 = x <= 10
        let c20 = x <= 20

        try solver.withTransaction {
            $0.addConstraint(c10)
            $0.addConstraint(c20)
        }

        solver.updateVariables()

        assertIsCloseTo(10, x)

        try solver.withTransaction {
            $0.removeConstraint(c10)
        }

        solver.updateVariables()

        assertIsCloseTo(20, x)

        try solver.withTransaction {
            $0.removeConstraint(c20)
        }
        solver.updateVariables()

        assertIsCloseTo(100, x)

        let c10again = x <= 10

        try solver.withTransaction {
            $0.addConstraint(c10again)
            $0.addConstraint(c10)
        }
        solver.updateVariables()

        assertIsCloseTo(10, x)

        try solver.withTransaction {
            $0.removeConstraint(c10)
        }
        solver.updateVariables()
        assertIsCloseTo(10, x)

        try solver.withTransaction {
            $0.removeConstraint(c10again)
        }
        solver.updateVariables()
        assertIsCloseTo(100, x)
    }

    func testAddDelete2() throws {
        let solver = Solver()
        let x = Variable("x")
        let y = Variable("y")

        try solver.withTransaction {
            $0.addConstraint((x == 100).setStrength(Strength.WEAK))
            $0.addConstraint((y == 120).setStrength(Strength.STRONG))
        }

        let c10 = x <= 10.0
        let c20 = x <= 20.0

        try solver.withTransaction {
            $0.addConstraint(c10)
            $0.addConstraint(c20)
        }
        solver.updateVariables()

        assertIsCloseTo(10, x)
        assertIsCloseTo(120, y)

        try solver.withTransaction {
            $0.removeConstraint(c10)
        }
        solver.updateVariables()

        assertIsCloseTo(20, x)
        assertIsCloseTo(120, y)

        let cxy = x * 2 == y
        try solver.withTransaction {
            $0.addConstraint(cxy)
        }
        solver.updateVariables()

        assertIsCloseTo(20, x)
        assertIsCloseTo(40, y)

        try solver.withTransaction {
            $0.removeConstraint(c20)
        }
        solver.updateVariables()

        assertIsCloseTo(60, x)
        assertIsCloseTo(120, y)

        try solver.withTransaction {
            $0.removeConstraint(cxy)
        }
        solver.updateVariables()

        assertIsCloseTo(100, x)
        assertIsCloseTo(120, y)
    }

    func testInconsistent1() {
        let solver = Solver()
        let x = Variable("x")

        do {
            try solver.withTransaction {
                $0.addConstraint(x == 10.0)
                $0.addConstraint(x == 5.0)
            }
            solver.updateVariables()
        } catch CassowaryError.unsatisfiableConstraint {
            // An error is expected
            return
        } catch {
            XCTFail("An unexpected error was encountered")
        }

        XCTFail("Should throw exception")
    }

    func testInconsistent2() {
        let solver = Solver()
        let x = Variable("x")

        do {
            try solver.withTransaction {
                $0.addConstraint(x >= 10)
                $0.addConstraint(x <= 5)
            }
            solver.updateVariables()
        } catch CassowaryError.unsatisfiableConstraint {
            // An error is expected
            return
        } catch {
            XCTFail("An unexpected error was encountered")
        }

        XCTFail("Should throw exception")
    }

    func testInconsistent3() {
        let solver = Solver()
        let w = Variable("w")
        let x = Variable("x")
        let y = Variable("y")
        let z = Variable("z")

        do {
            try solver.withTransaction {
                $0.addConstraint(w >= 10)
                $0.addConstraint(x >= w)
                $0.addConstraint(y >= x)
                $0.addConstraint(z >= y)
                $0.addConstraint(z >= 8)
                $0.addConstraint(z <= 4.0)
            }
            solver.updateVariables()
        } catch let error as CassowaryError {
            // An error is expected
            print(error.detailedDescription())
            return
        } catch {
            XCTFail("An unexpected error was encountered")
        }

        XCTFail("Should throw exception")
    }

    func testPaperExample() throws {
        let xl = Variable("xl")
        let xm = Variable("xm")
        let xr = Variable("xr")

        let solver = Solver()
        try solver.withTransaction {
            $0.addConstraint(xr <= 100)
            $0.addConstraint(xm * 2 == xl + xr)
            $0.addConstraint(xl + 10 <= xr)
            $0.addConstraint(0 <= xl)
        }

        solver.updateVariables()

        assertIsCloseTo(xl, 90.0)
        assertIsCloseTo(xm, 95.0)
        assertIsCloseTo(xr, 100.0)
    }

    func testEditExample() throws {
        let solver = Solver()

        let left = Variable("left")
        let mid = Variable("mid")
        let right = Variable("right")

        try solver.withTransaction {
            $0.addConstraint(mid == (left + right) / 2)
            $0.addConstraint(right == left + 10)
            $0.addConstraint(right <= 100)
            $0.addConstraint(left >= 0)

            $0.addEditVariable(mid, strength: Strength.STRONG)
            $0.suggestValue(mid, value: 2)
        }

        solver.updateVariables()

        assertIsCloseTo(left, 0.0)
        assertIsCloseTo(mid, 5.0)
        assertIsCloseTo(right, 10.0)
    }

    func testExample() throws {
        let x = Variable("x")
        let y = Variable("y")

        let solver = Solver()

        try solver.withTransaction {
            $0.addConstraint(x == y)
        }

        solver.updateVariables()

        assertIsCloseTo(x, y)
    }

    func testTops() throws {
        class Constrainable {
            let top = Variable("top")
            let height = Variable("height")
            var bottom: Expression {
                return top + height
            }
        }

        let parent = Constrainable()
        let child = Constrainable()

        let solver = Solver()

        try solver.withTransaction {
            $0.addConstraint(child.top == parent.top)
            $0.addConstraint(child.bottom == parent.bottom)
            $0.addEditVariable(child.height, strength: Strength.STRONG)
            $0.suggestValue(child.height, value: 24.0)
        }

        solver.updateVariables()

        assertIsCloseTo(parent.height, 24)
    }

    func testAddEditVariable() {
        let v = Variable("test")
        let solver = Solver()

        // Shouldn't be able to add with a REQUIRED strength
        XCTAssertThrowsError(try solver.withTransaction { $0.addEditVariable(v, strength: Strength.REQUIRED) })

        XCTAssertNoThrow(try solver.withTransaction { $0.addEditVariable(v, strength: Strength.STRONG) })

        // Should throw a DuplicateEditVariable error.
        XCTAssertThrowsError(try solver.withTransaction { $0.addEditVariable(v, strength: Strength.STRONG) })
    }

    func testRemoveEditVariable() {
        let v = Variable("test")

        let solver = Solver()

        // Should throw an error- the edit variable hasn't been added yet.
        XCTAssertThrowsError(try solver.withTransaction { $0.removeEditVariable(v) })

        XCTAssertNoThrow(try solver.withTransaction { $0.addEditVariable(v, strength: Strength.STRONG) })
        XCTAssertNoThrow(try solver.withTransaction { $0.removeEditVariable(v) })
    }

    func testSuggestValue() {
        let v = Variable("test")
        let solver = Solver()

        // Should throw an error, as it hasn't been added as an edit variable
        XCTAssertThrowsError(try solver.withTransaction { $0.suggestValue(v, value: 1.0) })

        XCTAssertNoThrow(try solver.withTransaction { $0.addEditVariable(v, strength: Strength.STRONG) })
        XCTAssertNoThrow(try solver.withTransaction { $0.suggestValue(v, value: 1.0) })
    }

    func testGreaterThanOrEqualConstraint() throws {
        let v1 = Variable("v1")
        let v2 = Variable("v2")
        let solver = Solver()

        try solver.withTransaction {
            $0.addConstraint(v2 >= v1 + 10)
            $0.addEditVariable(v1, strength: Strength.STRONG)
            $0.addEditVariable(v2, strength: Strength.MEDIUM)
            $0.suggestValue(v2, value: 0)
            $0.suggestValue(v1, value: 10)
        }

        solver.updateVariables()

        XCTAssertEqual(v1.value, 10.0)
        XCTAssertEqual(v2.value, 20.0)
    }
}
