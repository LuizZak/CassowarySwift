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

public final class Term: CustomStringConvertible, CassowaryDebugDescription {
    internal var _debugDesc: String?
    internal var debugDescription: String {
        if let debugDesc = _debugDesc {
            return debugDesc
        }
        let debugDesc = debugDescGenerator()
        _debugDesc = debugDesc
        return debugDesc
    }
    internal var debugDescGenerator: (() -> String) = { "" }
    
    internal func addingDebugDescription(_ desc: @autoclosure @escaping () -> String) -> Self {
        _debugDesc = nil
        debugDescGenerator = desc
        return self
    }

    public var variable: Variable
    public var coefficient: Double

    public var value: Double {
        return coefficient * variable.value
    }

    public init(variable: Variable, coefficient: Double) {
        self.variable = variable
        self.coefficient = coefficient
    }

    public var description: String {
        if coefficient.isApproximately(value: 1.0) {
            return variable.description
        } else {
            return "\(variable.description) * \(coefficient)"
        }
    }

    public convenience init(variable: Variable) {
        self.init(variable: variable, coefficient: 1.0)
    }
    
    
}
