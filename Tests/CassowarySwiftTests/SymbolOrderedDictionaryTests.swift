import XCTest
@testable import CassowarySwift

class SymbolOrderedDictionaryTests: XCTestCase {
    func testRemoveValueForKey() {
        var dict = SymbolOrderedDictionary<String>()
        dict.updateValue("1", forKey: Symbol(id: 1, symbolType: .external))
        dict.updateValue("2", forKey: Symbol(id: 2, symbolType: .external))
        dict.updateValue("3", forKey: Symbol(id: 3, symbolType: .external))

        XCTAssertEqual(dict.removeValue(forKey: Symbol(id: 1, symbolType: .external)), "1")
        XCTAssertEqual(dict.removeValue(forKey: Symbol(id: 2, symbolType: .external)), "2")
        XCTAssertEqual(dict.removeValue(forKey: Symbol(id: 3, symbolType: .external)), "3")
        XCTAssertNil(dict.removeValue(forKey: Symbol(id: 4, symbolType: .external)))
    }

    func testRemoveValueForKey_caching() {
        var dict = SymbolOrderedDictionary<String>()
        dict.updateValue("1", forKey: Symbol(id: 1, symbolType: .external))
        dict.updateValue("2", forKey: Symbol(id: 2, symbolType: .external))
        dict.updateValue("3", forKey: Symbol(id: 3, symbolType: .external))

        dict.removeValue(forKey: Symbol(id: 1, symbolType: .external))
        dict.removeValue(forKey: Symbol(id: 2, symbolType: .external))
        dict.removeValue(forKey: Symbol(id: 4, symbolType: .external))

        let ordered = Array(dict)
        XCTAssertEqual(ordered.count, 1)
        XCTAssertTrue(ordered[0] == (Symbol(id: 3, symbolType: .external), "3"), ordered.description)
    }

    func testRemoveValueForKey_performance() {
        let count = 50_000
        var dict = SymbolOrderedDictionary<String>()
        for index in 0..<count {
            dict[Symbol(id: index, symbolType: .external)] = index.description
        }

        measure {
            var copy = SymbolOrderedDictionary(dict)

            for index in 0..<count {
                copy.removeValue(forKey: Symbol(id: index % (count / 2), symbolType: .external))
            }
        }
    }

    func testRemoveOccurrencesOfValue_performance() {
        let count = 1_000
        var dict = SymbolOrderedDictionary<Int>()
        for index in 0..<count {
            dict[Symbol(id: index, symbolType: .external)] = index
        }

        measure {
            var copy = SymbolOrderedDictionary(dict)

            for index in 0..<count {
                copy.removeOccurrences(ofValue: index % (count / 2))
            }
        }
    }
}
