import XCTest
@testable import CassowarySwift

class OrderedDictionaryTests: XCTestCase {
    func testRemoveValueForKey() {
        let dict = OrderedDictionary<Int, String>()
        dict.updateValue("1", forKey: 1)
        dict.updateValue("2", forKey: 2)
        dict.updateValue("3", forKey: 3)
        
        XCTAssertEqual(dict.removeValue(forKey: 1), "1")
        XCTAssertEqual(dict.removeValue(forKey: 2), "2")
        XCTAssertEqual(dict.removeValue(forKey: 3), "3")
        XCTAssertNil(dict.removeValue(forKey: 4))
    }
    
    func testRemoveValueForKey_caching() {
        let dict = OrderedDictionary<Int, String>()
        dict.updateValue("1", forKey: 1)
        dict.updateValue("2", forKey: 2)
        dict.updateValue("3", forKey: 3)
        
        dict.removeValue(forKey: 1)
        dict.removeValue(forKey: 2)
        dict.removeValue(forKey: 4)
        
        XCTAssertEqual(dict.orderedEntries.count, 1)
        XCTAssertTrue(dict.orderedEntries[0] == (3, "3"), dict.orderedEntries.description)
    }
    
    func testRemoveValueForKey_performance() {
        let dict = OrderedDictionary<Int, String>()
        for index in 0..<5000 {
            dict.updateValue(index.description, forKey: index)
        }
        
        measure {
            let copy = OrderedDictionary(dict)
            
            for index in 0..<5000 {
                copy.removeValue(forKey: index % 2500)
            }
        }
    }
}
