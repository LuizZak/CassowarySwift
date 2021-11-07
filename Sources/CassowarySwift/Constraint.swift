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

/**
 This is a class that describes a constraint placed on a number of variables in the solver system.
 */

public class Constraint: CassowaryDebugDescription, CustomStringConvertible {
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

    public var description: String {
        if debugDescription.count > 0 {
            return "Constraint<\(debugDescription) | strength: \(Strength.readableString(strength)) | operator: \(op)>"
        }

        return "Constraint<(\(expression)) | strength: \(Strength.readableString(strength)) | operator: \(op)>"
    }

    /// The expression held by the constraint
    private(set) var expression: Expression

    /// The strength of the constraint
    public var strength: Double

    /// The operator of the constraint
    private(set) var op: RelationalOperator

    /// Create a constraint with the given expression and operator
    public convenience init(expr: Expression, op: RelationalOperator) {
        self.init(expr: expr, op: op, strength: Strength.REQUIRED)
    }

    /// Create a constraint with the given expression, operator and strength
    public init(expr: Expression, op: RelationalOperator, strength: Double) {
        self.expression = Constraint.reduce(expr)
        self.op = op
        self.strength = Strength.clip(strength)
    }

    /// Create a constraint, copying the provided constraint, with the given strength
    public convenience init(other: Constraint, strength: Double) {
        self.init(expr: other.expression, op: other.op, strength: strength)
    }

    private static func reduce(_ expr: Expression) -> Expression {
        var vars: [Variable: Double] = [:]

        for term in expr.terms {
            var value = vars[term.variable] ?? 0.0
            value += term.coefficient
            vars[term.variable] = value
        }

        // Keep ordering of terms to maintain a consistency specially in serialization
        let reducedTerms: [Term] = expr.terms.compactMap {
            if let coeff = vars.removeValue(forKey: $0.variable) {
                return $0.withCoefficient(coeff)
            }

            return nil
        }

        return Expression(terms: reducedTerms, constant: expr.constant)
    }

    /// Set the strength of the constraint
    public final func setStrength(_ newStrength: Double) -> Constraint {
        self.strength = newStrength
        return self
    }

    /// Returns `true` if this constraint is equivalent to another, down to the
    /// variable names referenced, the order of the terms, and the constant.
    internal func isEquivalent(to other: Constraint) -> Bool {
        guard strength == other.strength else {
            return false
        }
        guard expression.constant == other.expression.constant else {
            return false
        }
        guard expression.terms.count == other.expression.terms.count else {
            return false
        }

        return zip(expression.terms, other.expression.terms).allSatisfy { (t1, t2) in
            return t1.coefficient == t2.coefficient && t1.variable.name == t2.variable.name
        }
    }
}

// MARK: Equatable
extension Constraint: Equatable {
    public static func == (lhs: Constraint, rhs: Constraint) -> Bool {
        return lhs === rhs
    }
}

// MARK: Hashable
extension Constraint: Hashable {
    public func hash(into hasher: inout Hasher) {
        hasher.combine(ObjectIdentifier(self))
    }
}

// MARK: - EditConstraint
internal final class EditConstraint: Constraint {
    internal var suggestedValue: Double?

    override public var description: String {
        if debugDescription.count > 0 {
            return "EditConstraint<\(debugDescription) | Strength: \(Strength.readableString(strength))>"
        }

        return "EditConstraint<\(expression) == \(suggestedValue ?? 0) | Strength: \(Strength.readableString(strength))>"
    }
}
