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

class ConstraintTests: XCTestCase {
    func testInitConstraint() {
        let e1 = Expression(constant: 1.0)
        let c1 = Constraint(expr: e1, op: .equal)

        XCTAssertEqual(c1.op, .equal)
        XCTAssertEqual(c1.description, "Constraint<(1.0) | strength: REQUIRED | operator: equal>")

        // Creating a constraint from another constraint
        let c2 = Constraint(other: c1, strength: Strength.WEAK)
        XCTAssertEqual(c2.description, "Constraint<(1.0) | strength: WEAK | operator: equal>")
    }

    func testEditConstraint() {
        let e1 = Expression(constant: 1.0)
        var c1 = EditConstraint(expr: e1, op: .equal)
        c1.suggestedValue = 2.0
        XCTAssertEqual(c1.description, "EditConstraint<1.0 == 2.0 | Strength: REQUIRED>")

        c1 = c1.addingDebugDescription("Test")
        XCTAssertEqual(c1.description, "EditConstraint<Test | Strength: REQUIRED>")
    }

    func testHasSameEffectsAs() {
        let v1 = Variable("v1")
        let v2 = Variable("v2")
        let v2_2 = Variable("v2")
        let c1: Constraint = v1 == v2
        let c2: Constraint = v1 == v2
        let c3: Constraint = v1 == v2_2

        XCTAssertTrue(c1.hasSameEffects(as: c1))
        XCTAssertTrue(c1.hasSameEffects(as: c2))
        XCTAssertFalse(c1.hasSameEffects(as: c3))
        XCTAssertFalse(c2.hasSameEffects(as: c3))
    }

    func testIsEquivalentTo() {
        let v1 = Variable("v1")
        let v2 = Variable("v2")
        let v2_2 = Variable("v2")
        let c1: Constraint = v1 == v2
        let c2: Constraint = v1 == v2
        let c3: Constraint = v1 == v2_2

        XCTAssertTrue(c1.isEquivalent(to: c1))
        XCTAssertTrue(c1.isEquivalent(to: c2))
        XCTAssertTrue(c1.isEquivalent(to: c3))
        XCTAssertTrue(c2.isEquivalent(to: c3))
    }
}
