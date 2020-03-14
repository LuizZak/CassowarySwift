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
@testable import Cassowary

class VariableTests: XCTestCase {
    
    func testConstructors() {
        let x = Variable("x")
        
        XCTAssertEqual(x.name, "x")
        assertIsCloseTo(x, 0.0)
        
        XCTAssertEqual(x.description, "x")
        
        let y = Variable(1234.5678)
        assertIsCloseTo(y, 1234.5678)
        XCTAssertEqual(y.name, "1234.5678")
        
        y.value = 8765.4321
        assertIsCloseTo(y, 8765.4321)
    }
    
    func testVariableLessThanOrEqualOperator() {
        let x = Variable("x")
        
        let constraint = x <= x
        
        XCTAssertEqual(constraint.op, .lessThanOrEqual)
    }
    
    func testVariableLessThanOrEqualConstantOperator() {
        let x = Variable("x")
        
        let constraint = x <= x + 10
        
        XCTAssertEqual(constraint.op, .lessThanOrEqual)
    }
    
    func testVariableGreaterThanOrEqualOperator() {
        let x = Variable("x")
        
        let constraint = x >= x
        
        XCTAssertEqual(constraint.op, .greaterThanOrEqual)
    }
    
    func testVariableGreaterThanOrEqualConstantOperator() {
        let x = Variable("x")
        
        let constraint = x >= x + 10
        
        XCTAssertEqual(constraint.op, .greaterThanOrEqual)
    }
}

