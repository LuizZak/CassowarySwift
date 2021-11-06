/// An ordered dictionary of symbol-keyed values.
final class SymbolOrderedDictionary<ValueType>: ExpressibleByDictionaryLiteral {
    typealias KeyType = Symbol

    private(set) var keys = [KeyType]()
    private var dictionary = [Int: ValueType]()

    var count: Int { return keys.count }

    internal var _cachedOrderedEntries: [(key: KeyType, value: ValueType)]? = nil

    var orderedEntries: [(key: KeyType, value: ValueType)] {
        if _cachedOrderedEntries == nil {
            _cachedOrderedEntries = keys.map {
                (key: $0, value: dictionary[$0.id]!)
            }
        }
        return _cachedOrderedEntries!
    }

    subscript(key: KeyType) -> ValueType? {
        get { return self.dictionary[key.id] }
        set {
            if let v = newValue {
                updateValue(v, forKey: key)
            } else {
                removeValue(forKey: key)
            }
        }
    }

    required init(dictionaryLiteral elements: (KeyType, ValueType)...) {
        for (k, v) in elements {
            self[k] = v
        }
    }

    init(_ dict: SymbolOrderedDictionary<ValueType>) {
        self.keys = dict.keys
        self.dictionary = dict.dictionary
        self._cachedOrderedEntries = dict._cachedOrderedEntries
    }

    private init(keys: [KeyType], dictionary: [Int: ValueType]) {
        self.keys = keys
        self.dictionary = dictionary
    }

    func updateValue(_ value: ValueType, forKey key: KeyType) {
        let oldVal = dictionary.updateValue(value, forKey: key.id)

        if oldVal == nil {
            keys.append(key)
            _cachedOrderedEntries?.append((key, value))
        } else {
            _cachedOrderedEntries = nil
        }
    }

    @discardableResult
    func removeValue(forKey key: KeyType) -> ValueType? {
        guard let removed = dictionary.removeValue(forKey: key.id) else {
            return nil
        }

        if let index = index(forKey: key) {
            _cachedOrderedEntries?.remove(at: index)
            keys.remove(at: index)
        }

        return removed
    }

    func mapValues<T>(_ closure: (ValueType) -> T) -> SymbolOrderedDictionary<T> {
        let newValues = dictionary.mapValues(closure)

        return SymbolOrderedDictionary<T>(keys: keys, dictionary: newValues)
    }

    func index(forKey key: KeyType) -> Int? {
        return keys.firstIndex { $0 == key }
    }
}
