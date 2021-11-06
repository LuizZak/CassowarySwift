import Foundation

/// A JSON value.
enum JSON: Codable {
    /// A dictionary of string-keyed JSON values
    case dictionary([String: JSON])
    /// An array of JSON values
    case array([JSON])
    /// A string of characters
    case string(String)
    /// A Double number
    case number(Double)
    /// A boolean value
    case bool(Bool)
    /// The JSON `null` value
    case null

    init(from decoder: Decoder) throws {
        if let container = try? decoder.container(keyedBy: JSONKey.self) {
            var dict: [String: JSON] = .init(minimumCapacity: container.allKeys.count)
            for key in container.allKeys {
                dict[key.stringValue] = try container.decode(JSON.self, forKey: key)
            }
            self = .dictionary(dict)
            return
        }
        if var container = try? decoder.unkeyedContainer() {
            var array: [JSON] = []
            if let count = container.count {
                array.reserveCapacity(count)
            }
            while !container.isAtEnd {
                array.append(try container.decode(JSON.self))
            }
            self = .array(array)
            return
        }
        let singleValue = try decoder.singleValueContainer()
        if let number = try? singleValue.decode(Double.self) {
            self = .number(number)
        } else if let number = try? singleValue.decode(Int.self) {
            self = .number(Double(number))
        } else if let string = try? singleValue.decode(String.self) {
            self = .string(string)
        } else if let bool = try? singleValue.decode(Bool.self) {
            self = .bool(bool)
        } else if singleValue.decodeNil() {
            self = .null
        } else {
            throw DecodingError.dataCorruptedError(in: singleValue,
                                                   debugDescription: "Not a valid JSON value")
        }
    }

    func encode(to encoder: Encoder) throws {
        switch self {
        case .dictionary(let dict):
            var container = encoder.container(keyedBy: JSONKey.self)
            for (key, value) in dict.sorted(by: { $0.key < $1.key }) {
                try container.encode(value, forKey: .string(key))
            }
            return
        case .array(let array):
            var container = encoder.unkeyedContainer()
            for value in array {
                try container.encode(value)
            }
            return
        case .number(let number):
            var container = encoder.singleValueContainer()
            try container.encode(number)
        case .string(let string):
            var container = encoder.singleValueContainer()
            try container.encode(string)
        case .bool(let bool):
            var container = encoder.singleValueContainer()
            try container.encode(bool)
        case .null:
            var container = encoder.singleValueContainer()
            try container.encodeNil()
        }
    }
    
    init<T: Encodable>(fromEncodable encodable: T) throws {
        let encoder = JSONEncoder()
        let data = try encoder.encode(encodable)
        
        let decoder = JSONDecoder()
        
        self = try decoder.decode(JSON.self, from: data)
    }
    
    init(data: Data) throws {
        let decoder = JSONDecoder()
        
        self = try decoder.decode(JSON.self, from: data)
    }
    
    func decode<T: Decodable>(_ decodable: T.Type = T.self) throws -> T {
        let data = try asData()
        
        let decoder = JSONDecoder()
        
        return try decoder.decode(T.self, from: data)
    }
    
    func asData() throws -> Data {
        let encoder = JSONEncoder()
        return try encoder.encode(self)
    }
    
    enum JSONType: String {
        case dictionary
        case array
        case string
        case number
        case bool
        case null
    }
}

extension JSON: Equatable { }
extension JSON: Hashable { }

extension JSON: CustomStringConvertible {
    var description: String {
        switch self {
        case .dictionary(let dictionary):
            return "{" + dictionary.sorted(by: { $0.key < $1.key }).map {
                #""\#($0)": \#($1)"#
            }.joined(separator: ", ") + "}"
        case .array(let array):
            return "[" + array.map(\.description).joined(separator: ", ") + "]"
        case .string(let string):
            return #""\#(string)""#
        case .number(let double):
            return double.description
        case .bool(let bool):
            return bool.description
        case .null:
            return "null"
        }
    }
}

extension JSON {
    /// Returns this JSON value's type
    var type: JSONType {
        switch self {
        case .dictionary:
            return .dictionary
        case .array:
            return .array
        case .string:
            return .string
        case .number:
            return .number
        case .bool:
            return .bool
        case .null:
            return .null
        }
    }
}

extension JSON {
    /// Returns the dictionary of values for this `JSON` in case it is a dictionary,
    /// `nil` otherwise.
    var dictionary: [String: JSON]? {
        switch self {
        case .dictionary(let dict):
            return dict
        default:
            return nil
        }
    }
    
    /// Returns the array of subvalues for this `JSON` in case it is an array,
    /// `nil` otherwise.
    var array: [JSON]? {
        switch self {
        case .array(let array):
            return array
        default:
            return nil
        }
    }
    
    /// Returns a string for this `JSON` in case it is a string, `nil` otherwise.
    var string: String? {
        switch self {
        case .string(let string):
            return string
        default:
            return nil
        }
    }
    
    /// Returns a `Double` for this `JSON` in case it is a number, `nil` otherwise.
    var double: Double? {
        switch self {
        case .number(let number):
            return number
        default:
            return nil
        }
    }
    
    /// Returns a boolean for this `JSON` in case it is a bool, `nil` otherwise.
    var bool: Bool? {
        switch self {
        case .bool(let bool):
            return bool
        default:
            return nil
        }
    }
    
    /// Returns an integer for this `JSON` in case it is a number that is losslesly
    /// convertible to `Int`, `nil` otherwise.
    var int: Int? {
        switch self {
        case .number(let number):
            return Int(exactly: number)
        default:
            return nil
        }
    }
}

extension JSON: ExpressibleByArrayLiteral {
    init(arrayLiteral elements: JSON...) {
        self = .array(elements)
    }
}

extension JSON: ExpressibleByDictionaryLiteral {
    init(dictionaryLiteral elements: (String, JSON)...) {
        var dict: [String: JSON] = .init(minimumCapacity: elements.count)
        elements.forEach { dict[$0] = $1 }
        self = .dictionary(dict)
    }
}

extension JSON: ExpressibleByFloatLiteral {
    init(floatLiteral value: Double) {
        self = .number(value)
    }
}

extension JSON: ExpressibleByIntegerLiteral {
    init(integerLiteral value: Int) {
        self = .number(Double(value))
    }
}

extension JSON: ExpressibleByBooleanLiteral {
    init(booleanLiteral value: Bool) {
        self = .bool(value)
    }
}

extension JSON: ExpressibleByStringLiteral {
    init(stringLiteral value: String) {
        self = .string(value)
    }
}

extension JSON: ExpressibleByNilLiteral {
    init(nilLiteral: ()) {
        self = .null
    }
}

enum JSONKey: CodingKey {
    case int(Int)
    case string(String)

    init?(intValue: Int) {
        self = .int(intValue)
    }
    init?(stringValue: String) {
        self = .string(stringValue)
    }

    var intValue: Int? {
        switch self {
        case .int(let int):
            return int
        case .string:
            return nil
        }
    }

    var stringValue: String {
        switch self {
        case .int(let int):
            return int.description
        case .string(let string):
            return string
        }
    }
}

extension JSON: Collection {
    enum JSONIndexKey: Comparable {
        case array(Int)
        case dictionary(Dictionary<String, JSON>.Index)
        case null

        static func == (lhs: Index, rhs: Index) -> Bool {
            switch (lhs, rhs) {
            case (.array(let left), .array(let right)):
                return left == right
            case (.dictionary(let left), .dictionary(let right)):
                return left == right
            case (.null, .null):
                return true
            default:
                return false
            }
        }

        static func < (lhs: Index, rhs: Index) -> Bool {
            switch (lhs, rhs) {
            case (.array(let left), .array(let right)):
                return left < right
            case (.dictionary(let left), .dictionary(let right)):
                return left < right
            default:
                return false
            }
        }
    }

    typealias Index = JSONIndexKey
    typealias Element = (String, JSON)

    var startIndex: Index {
        switch self {
        case .array(let array):
            return .array(array.startIndex)
        case .dictionary(let dict):
            return .dictionary(dict.startIndex)
        default:
            return .null
        }
    }

    var endIndex: Index {
        switch self {
        case .array(let array):
            return .array(array.endIndex)
        case .dictionary(let dict):
            return .dictionary(dict.endIndex)
        default:
            return .null
        }
    }

    func index(after i: Index) -> Index {
        switch (self, i) {
        case (.array(let array), .array(let index)):
            return .array(array.index(after: index))
        case (.dictionary(let dict), .dictionary(let index)):
            return .dictionary(dict.index(after: index))
        default:
            return .null
        }
    }

    subscript(position: Index) -> (String, JSON) {
        switch (self, position) {
        case (.array(let array), .array(let index)):
            return (String(index), array[index])
        case (.dictionary(let dict), .dictionary(let index)):
            return (dict[index].key, dict[index].value)
        default:
            return ("", .null)
        }
    }

    subscript(key: String) -> JSON? {
        get {
            switch self {
            case .dictionary(let dict):
                return dict[key]
            default:
                return nil
            }
        }
        set {
            switch self {
            case .dictionary(var dict):
                dict[key] = newValue
                self = .dictionary(dict)
            default:
                break
            }
        }
    }

    subscript(index: Int) -> JSON {
        get {
            switch self {
            case .array(let array):
                return array[index]
            default:
                return .null
            }
        }
        set {
            switch self {
            case .array(var array):
                array[index] = newValue
                self = .array(array)
            default:
                break
            }
        }
    }

    subscript(path path: JSONIndexer...) -> JSONSubscriptAccess {
        let accesses = path.map { $0.jsonIndex }
        
        var json: JSON = self
        
        for (i, access) in accesses.enumerated() {
            switch access {
            case .dictionary(let key):
                if let value = json[key] {
                    json = value
                } else if json.type == .dictionary {
                    return .keyNotFound(Array(accesses[...i]))
                } else {
                    return .notADictionary(Array(accesses[..<i]))
                }
            case .index(let index):
                if let array = json.array, index >= 0 && index < array.count {
                    json = array[index]
                } else if json.type == .array {
                    return .keyNotFound(Array(accesses[...i]))
                } else {
                    return .notAnArray(Array(accesses[..<i]))
                }
            }
        }
        
        return .value(json)
    }
}

protocol JSONIndexer {
    var jsonIndex: JSONSubscriptAccess.JSONAccess { get }
}

extension String: JSONIndexer {
    var jsonIndex: JSONSubscriptAccess.JSONAccess {
        return .dictionary(self)
    }
}

extension Int: JSONIndexer {
    var jsonIndex: JSONSubscriptAccess.JSONAccess {
        return .index(self)
    }
}

enum JSONSubscriptAccess: Equatable {
    case value(JSON)
    case notAnArray([JSONAccess])
    case notADictionary([JSONAccess])
    case keyNotFound([JSONAccess])
    
    var json: JSON? {
        switch self {
        case .value(let json):
            return json
        default:
            return nil
        }
    }
    
    /// Attempts to read this subscript access as a decimal value, throwing an
    /// error if the keypath is invalid, or if the value is not a `Double`.
    var number: Double {
        get throws {
            switch self {
            case .value(let v):
                if let double = v.double {
                    return double
                }
                
                throw Error.invalidValueType
                
            case let .keyNotFound(path),
                 let .notADictionary(path),
                 let .notAnArray(path):
                
                throw Error.invalidPath(path)
            }
        }
    }
    
    /// Attempts to read this subscript access as an integer, throwing an
    /// error if the keypath is invalid, or if the value is not a `Integer`.
    var integer: Int {
        get throws {
            switch self {
            case .value(let v):
                if let double = v.double {
                    return Int(double)
                }
                
                throw Error.invalidValueType
                
            case let .keyNotFound(path),
                 let .notADictionary(path),
                 let .notAnArray(path):
                
                throw Error.invalidPath(path)
            }
        }
    }
    
    /// Attempts to read this subscript access as a string, throwing an
    /// error if the keypath is invalid, or if the value is not a `String`.
    var string: String {
        get throws {
            switch self {
            case .value(let v):
                if let string = v.string {
                    return string
                }
                
                throw Error.invalidValueType
                
            case let .keyNotFound(path),
                 let .notADictionary(path),
                 let .notAnArray(path):
                
                throw Error.invalidPath(path)
            }
        }
    }
    
    /// Attempts to read this subscript access as a boolean value, throwing an
    /// error if the keypath is invalid, or if the value is not a `Bool`.
    var bool: Bool {
        get throws {
            switch self {
            case .value(let v):
                if let bool = v.bool {
                    return bool
                }
                
                throw Error.invalidValueType
                
            case let .keyNotFound(path),
                 let .notADictionary(path),
                 let .notAnArray(path):
                
                throw Error.invalidPath(path)
            }
        }
    }
    
    /// Attempts to read this subscript access as an array value, throwing an
    /// error if the keypath is invalid, or if the value is not an array.
    var array: [JSON] {
        get throws {
            switch self {
            case .value(let v):
                if let array = v.array {
                    return array
                }
                
                throw Error.invalidValueType
                
            case let .keyNotFound(path),
                 let .notADictionary(path),
                 let .notAnArray(path):
                
                throw Error.invalidPath(path)
            }
        }
    }
    
    /// Attempts to read this subscript access as a dictionary value, throwing an
    /// error if the keypath is invalid, or if the value is not a dictionary.
    var dictionary: [String: JSON] {
        get throws {
            switch self {
            case .value(let v):
                if let dictionary = v.dictionary {
                    return dictionary
                }
                
                throw Error.invalidValueType
                
            case let .keyNotFound(path),
                 let .notADictionary(path),
                 let .notAnArray(path):
                
                throw Error.invalidPath(path)
            }
        }
    }
    
    /// Returns whether this keypath access points to a `null ` JSON value.
    var isNull: Bool {
        get {
            switch self {
            case .value(let v):
                return v == .null
                
            default:
                return false
            }
        }
    }
    
    /// Returns whether this keypath access leads to a valid JSON value within
    /// the original JSON being accessed.
    var isValidKeypath: Bool {
        switch self {
        case .value:
            return true
        default:
            return false
        }
    }
    
    func decode<T: Decodable>(_ decodable: T.Type = T.self) throws -> T {
        switch self {
        case .value(let v):
            return try v.decode()
            
        case let .keyNotFound(path),
             let .notADictionary(path),
             let .notAnArray(path):
            
            throw Error.invalidPath(path)
        }
    }
    
    enum JSONAccess: Equatable {
        case index(Int)
        case dictionary(String)
    }
    
    enum Error: Swift.Error {
        case invalidPath([JSONAccess])
        case invalidValueType
    }
}

protocol JSONConvertible {
    var json: JSON { get }
}

extension JSON: JSONConvertible {
    var json: JSON { self }
}
extension String: JSONConvertible {
    var json: JSON { .string(self) }
}
extension Double: JSONConvertible {
    var json: JSON { .number(self) }
}
extension Int: JSONConvertible {
    var json: JSON { .number(Double(self)) }
}
extension Bool: JSONConvertible {
    var json: JSON { .bool(self) }
}
extension Array: JSONConvertible where Element: JSONConvertible {
    var json: JSON {
        .array(self.map { $0.json })
    }
}
extension Dictionary: JSONConvertible where Key == String, Value: JSONConvertible {
    var json: JSON {
        .dictionary(mapValues { $0.json })
    }
}
