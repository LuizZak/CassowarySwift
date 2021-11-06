/// An ordered dictionary of symbol-keyed values.
struct SymbolOrderedDictionary<ValueType>: ExpressibleByDictionaryLiteral {
    private var dictionary = [Int: ValueType]()

    private(set) var _cache: OrderedEntriesCache = OrderedEntriesCache(value: nil)
    private(set) var keys = [Symbol]()

    var count: Int { return keys.count }

    /// Returns a list of unordered values in this ordered dictionary.
    var unorderedValues: [ValueType] {
        return Array(dictionary.values)
    }

    subscript(key: Symbol) -> ValueType? {
        @_transparent
        get { return self.dictionary[key.id] }
        @_transparent
        set {
            if let v = newValue {
                updateValue(v, forKey: key)
            } else {
                removeValue(forKey: key)
            }
        }
    }

    @_transparent
    init(dictionaryLiteral elements: (Symbol, ValueType)...) {
        for (k, v) in elements {
            self[k] = v
        }
    }

    @_transparent
    init(_ other: SymbolOrderedDictionary<ValueType>) {
        self.keys = other.keys
        self.dictionary = other.dictionary
        self._cache = other._cache
    }

    @_transparent
    private init(keys: [Symbol], dictionary: [Int: ValueType]) {
        self.keys = keys
        self.dictionary = dictionary
    }

    mutating func ensureUnique() {
        if !isKnownUniquelyReferenced(&_cache) {
            _cache = _cache.copy()
        }
    }

    mutating func updateValue(_ value: ValueType, forKey key: Symbol) {
        ensureUnique()

        let oldVal = dictionary.updateValue(value, forKey: key.id)

        if oldVal == nil {
            keys.append(key)
            _cache.value?.append((key, value))
        } else {
            _cache.value = nil
        }
    }

    /// Removes all occurrences of a given value from this dictionary
    mutating func removeOccurrences(ofValue value: ValueType) where ValueType: Equatable {
        ensureUnique()

        for (i, k) in keys.enumerated().reversed() {
            if dictionary[k.id] == value {
                dictionary.removeValue(forKey: k.id)
                keys.remove(at: i)
                _cache.value?.remove(at: i)
            }
        }
    }

    @discardableResult
    mutating func removeValue(forKey key: Symbol) -> ValueType? {
        guard let removed = dictionary.removeValue(forKey: key.id) else {
            return nil
        }

        if let index = index(forKey: key) {
            ensureUnique()

            _cache.value?.remove(at: index)
            keys.remove(at: index)
        }

        return removed
    }

    func mapValues<T>(_ closure: (ValueType) -> T) -> SymbolOrderedDictionary<T> {
        let newValues = dictionary.mapValues(closure)

        return SymbolOrderedDictionary<T>(keys: keys, dictionary: newValues)
    }

    @_transparent
    func index(forKey key: Symbol) -> Int? {
        return keys.firstIndex { $0 == key }
    }

    class OrderedEntriesCache {
        var value: [(key: Symbol, value: ValueType)]?

        init(value: [(key: Symbol, value: ValueType)]?) {
            self.value = value
        }

        func copy() -> OrderedEntriesCache {
            return OrderedEntriesCache(value: value)
        }
    }
}

extension SymbolOrderedDictionary: Sequence {
    #if ORDERED_DICTIONARY_ITERATOR

    var orderedEntries: Iterator {
        return Iterator(keys: keys, dictionary: dictionary)
    }

    func makeIterator() -> Iterator {
        return Iterator(keys: keys, dictionary: dictionary)
    }

    struct Iterator: IteratorProtocol {
        typealias Element = (key: Symbol, value: Value)

        var keyIterator: Array<Symbol>.Iterator
        var dictionary: [Int: Value]

        fileprivate init(keys: [Symbol], dictionary: [Int: Value]) {
            keyIterator = keys.makeIterator()
            self.dictionary = dictionary
        }

        mutating func next() -> (key: Symbol, value: ValueType)? {
            guard let next = keyIterator.next() else {
                return nil
            }

            return (key: next, value: dictionary[next.id].unsafelyUnwrapped)
        }
    }

    #else

    func makeIterator() -> IndexingIterator<[(key: Symbol, value: ValueType)]> {
        if _cache.value == nil {
            _cache.value = keys.map {
                (key: $0, value: dictionary[$0.id].unsafelyUnwrapped)
            }
        }

        return _cache.value.unsafelyUnwrapped.makeIterator()
    }

    #endif
}
