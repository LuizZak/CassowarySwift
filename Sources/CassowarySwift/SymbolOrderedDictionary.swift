#if UNORDERED_DICTIONARY

typealias SymbolOrderedDictionary<ValueType> = Dictionary<Symbol, ValueType>

#else // UNORDERED_DICTIONARY

/// An ordered dictionary of symbol-keyed values.
struct SymbolOrderedDictionary<ValueType>: ExpressibleByDictionaryLiteral {
    private var dictionary = [Int: ValueType]()

    private(set) var _cache: OrderedEntriesCache = OrderedEntriesCache(value: nil)
    private(set) var keys = [Symbol]()

    var count: Int { return keys.count }

    /// Returns a list of unordered values in this ordered dictionary.
    var values: Dictionary<Int, ValueType>.Values {
        return dictionary.values
    }

    subscript(key: Symbol) -> ValueType? {
        get { return self.dictionary[key.id] }
        set {
            if let v = newValue {
                updateValue(v, forKey: key)
            } else {
                removeValue(forKey: key)
            }
        }
        _modify {
            yield &self.dictionary[key.id]
        }
    }

    init(dictionaryLiteral elements: (Symbol, ValueType)...) {
        for (k, v) in elements {
            self[k] = v
        }
    }

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
    typealias Element = (key: Symbol, value: ValueType)

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

            return (key: next, value: dictionary[next.id]!)
        }
    }

    #else // ORDERED_DICTIONARY_ITERATOR

    func makeIterator() -> IndexingIterator<[(key: Symbol, value: ValueType)]> {
        let cached = _cache.value ?? keys.map {
            (key: $0, value: dictionary[$0.id]!)
        }
        _cache.value = cached

        return cached.makeIterator()
    }

    #endif // ORDERED_DICTIONARY_ITERATOR
}

extension SymbolOrderedDictionary: Collection {
    typealias Index = Int

    subscript(position: Int) -> (key: Symbol, value: ValueType) {
        get {
            let key = keys[position]
            return (key, dictionary[key.id]!)
        }
    }

    var startIndex: Int { 0 }

    var endIndex: Int { keys.count }

    var isEmpty: Bool { keys.isEmpty }

    var underestimatedCount: Int { keys.underestimatedCount }

    func index(after i: Int) -> Int {
        assert(i < endIndex)

        return i + 1
    }
}

#endif // UNORDERED_DICTIONARY
