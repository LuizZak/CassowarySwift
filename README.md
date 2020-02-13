# Cassowary Swift

A Swift port of the Cassowary linear constraints solver. Tested on OS X, iOS and Linux.

# Example usage


```swift
let solver = Solver()

let left =  Variable("left")
let mid =   Variable("mid")
let right = Variable("right")

try solver.addConstraint(mid == (left + right) / 2)
try solver.addConstraint(right == left + 10)
try solver.addConstraint(right <= 100)
try solver.addConstraint(left >= 0)

solver.updateVariables()

// left.value is now 90.0
// mid.value is now 95.0
// right.value is now 100.0

try solver.addEditVariable(variable: mid, strength: Strength.STRONG)
try solver.suggestValue(variable: mid, value: 2)

solver.updateVariables()

// left.value is now 0.0
// mid.value is now 5.0
// right.value is now 10.0

```

# Acknowledgements
Cassowary Swift originally started as a direct port of [kiwi-java](https://github.com/alexbirkett/kiwi-java) by [Alex Birkett](https://github.com/alexbirkett)

This repo is a fork of the original code from [Tribal Worldwide London](https://github.com/tribalworldwidelondon/CassowarySwift)
