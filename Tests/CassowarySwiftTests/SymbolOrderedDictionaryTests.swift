import XCTest
@testable import CassowarySwift

class SymbolOrderedDictionaryTests: XCTestCase {
    func testRemoveValueForKey() {
        let dict = SymbolOrderedDictionary<String>()
        dict.updateValue("1", forKey: Symbol(id: 1, .external))
        dict.updateValue("2", forKey: Symbol(id: 2, .external))
        dict.updateValue("3", forKey: Symbol(id: 3, .external))

        XCTAssertEqual(dict.removeValue(forKey: Symbol(id: 1, .external)), "1")
        XCTAssertEqual(dict.removeValue(forKey: Symbol(id: 2, .external)), "2")
        XCTAssertEqual(dict.removeValue(forKey: Symbol(id: 3, .external)), "3")
        XCTAssertNil(dict.removeValue(forKey: Symbol(id: 4, .external)))
    }

    func testRemoveValueForKey_caching() {
        let dict = SymbolOrderedDictionary<String>()
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
        let dict = SymbolOrderedDictionary<String>()
        for index in 0..<5000 {
            dict.updateValue(index.description, forKey: Symbol(id: index, .external))
        }

        measure {
            let copy = SymbolOrderedDictionary(dict)

            for index in 0..<5000 {
                copy.removeValue(forKey: Symbol(id: index % 2500, .external))
            }
        }
    }
}
