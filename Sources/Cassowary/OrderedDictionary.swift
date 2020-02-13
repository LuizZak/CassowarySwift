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

// Based on the implementation by Michael Kyriacou at
// http://codeforcaffeine.com/programming/swift-3-ordered-dictionary/

internal final class OrderedDictionary<KeyType: Hashable, ValueType>: ExpressibleByDictionaryLiteral {
    @usableFromInline
    var keys = [KeyType]()
    @usableFromInline
    var dictionary = [KeyType: ValueType]()
    
    public var count: Int { return keys.count }
    
    @usableFromInline
    internal var _cachedOrderedEntries: [(key: KeyType, value: ValueType)]? = nil
    
    @inlinable
    var orderedEntries: [(key: KeyType, value: ValueType)] {
        if _cachedOrderedEntries == nil {
            _cachedOrderedEntries = keys.map {
                (key: $0, value: dictionary[$0]!)
            }
        }
        return _cachedOrderedEntries!
    }
    
    required init(dictionaryLiteral elements: (KeyType, ValueType)...) {
        for (k, v) in elements {
            self[k] = v
        }
    }
    
    @inlinable
    subscript(key: KeyType) -> ValueType? {
        get { return self.dictionary[key] }
        set {
            if let v = newValue {
                updateValue(v, forKey: key)
            } else {
                removeValue(forKey: key)
            }
        }
    }
    
    init(_ dict: OrderedDictionary<KeyType, ValueType>) {
        self.keys = dict.keys
        self.dictionary = dict.dictionary
    }
    
    private init(keys: [KeyType], dictionary: [KeyType: ValueType]) {
        self.keys = keys
        self.dictionary = dictionary
    }
    
    @inlinable
    func updateValue(_ value: ValueType, forKey key: KeyType) {
        _cachedOrderedEntries = nil
        
        let oldVal = dictionary.updateValue(value, forKey: key)
        if oldVal == nil {
            keys.append(key)
        }
    }
    
    @inlinable
    func removeValue(forKey key: KeyType) {
        _cachedOrderedEntries = nil
        dictionary.removeValue(forKey: key)
        if let index = index(forKey: key) {
            keys.remove(at: index)
        }
    }
    
    @inlinable
    func mapValues<T>(_ closure: (ValueType) -> T) -> OrderedDictionary<KeyType, T> {
        let newValues = dictionary.mapValues(closure)
        
        return OrderedDictionary<KeyType, T>(keys: keys, dictionary: newValues)
    }
    
    @usableFromInline
    func index(forKey key: KeyType) -> Int? {
        return keys.firstIndex { $0 == key }
    }
}
