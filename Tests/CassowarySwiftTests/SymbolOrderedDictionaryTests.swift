import XCTest
@testable import CassowarySwift

class SymbolOrderedDictionaryTests: XCTestCase {
    func testRemoveValueForKey() {
        var dict = SymbolOrderedDictionary<String>()
        dict.updateValue("1", forKey: Symbol(id: 1, .external))
        dict.updateValue("2", forKey: Symbol(id: 2, .external))
        dict.updateValue("3", forKey: Symbol(id: 3, .external))

        XCTAssertEqual(dict.removeValue(forKey: Symbol(id: 1, .external)), "1")
        XCTAssertEqual(dict.removeValue(forKey: Symbol(id: 2, .external)), "2")
        XCTAssertEqual(dict.removeValue(forKey: Symbol(id: 3, .external)), "3")
        XCTAssertNil(dict.removeValue(forKey: Symbol(id: 4, .external)))
    }

    func testRemoveValueForKey_caching() {
        var dict = SymbolOrderedDictionary<String>()
        dict.updateValue("1", forKey: Symbol(id: 1, .external))
        dict.updateValue("2", forKey: Symbol(id: 2, .external))
        dict.updateValue("3", forKey: Symbol(id: 3, .external))

        dict.removeValue(forKey: Symbol(id: 1, .external))
        dict.removeValue(forKey: Symbol(id: 2, .external))
        dict.removeValue(forKey: Symbol(id: 4, .external))

        XCTAssertEqual(dict.orderedEntries.count, 1)
        XCTAssertTrue(dict.orderedEntries[0] == (Symbol(id: 3, .external), "3"), dict.orderedEntries.description)
    }

    func testRemoveValueForKey_performance() {
        let count = 50_000
        var dict = SymbolOrderedDictionary<String>()
        for index in 0..<count {
            dict[Symbol(id: index, .external)] = index.description
        }

        measure {
            var copy = SymbolOrderedDictionary(dict)

            for index in 0..<count {
                copy.removeValue(forKey: Symbol(id: index % (count / 2), .external))
            }
        }
    }

    func testRemoveOccurrencesOfValue_performance() {
        let count = 1_000
        var dict = SymbolOrderedDictionary<Int>()
        for index in 0..<count {
            dict[Symbol(id: index, .external)] = index
        }

        measure {
            var copy = SymbolOrderedDictionary(dict)

            for index in 0..<count {
                copy.removeOccurrences(ofValue: index % (count / 2))
            }
        }
    }
}
