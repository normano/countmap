#![deny(missing_docs)]
//! A map that helps counting elements.

use std::borrow::Borrow;
use std::collections::HashMap;
use std::collections::hash_map::{Drain, IntoIter, Iter, IterMut, Keys, RandomState, Values};
use std::hash::{BuildHasher, Hash};
use std::iter::FromIterator;
use std::ops::Index;

/// A count map is a hash map where the value field is a constantly incremented counter. If a key
/// is inserted for the first time, the counter is set to 1. Every subsequent insert will increment
/// the counter by 1. This implementation just acts as a decorator around a `HashMap` and exposes
/// almost the complete API of `HashMap` except things like `iter_mut()` or `get_mut()` since it
/// doesn't make sense in this use case.
#[derive(Clone, Debug)]
pub struct CountMap<K, S = RandomState>
where
    K: Eq + Hash,
    S: BuildHasher,
{
    map: HashMap<K, u64, S>,
}

impl<K> CountMap<K, RandomState>
where
    K: Eq + Hash,
{
    /// Creates an empty `CountMap`.
    ///
    /// # Examples
    /// ```
    /// use countmap::CountMap;
    ///
    /// let mut count_map: CountMap<&str> = CountMap::new();
    /// ```
    pub fn new() -> Self {
        Self::default()
    }

    /// Creates an empty `CountMap` with the specified capacity.
    ///
    /// The created map can hold at least `cap` elements before reallocating. If `cap` is `0` the
    /// map will not allocate.
    ///
    /// # Examples
    /// ```
    /// use countmap::CountMap;
    ///
    /// let mut count_map: CountMap<&str> = CountMap::with_capacity(10);
    /// ```
    pub fn with_capacity(cap: usize) -> Self {
        Self { map: HashMap::with_capacity(cap) }
    }
}

impl<K, S> CountMap<K, S>
where
    K: Eq + Hash,
    S: BuildHasher,
{
    /// Creates an empty `CountMap` which will use the given hash builder to hash keys.
    ///
    /// The created map has the default initial capacity.
    ///
    /// Warning: `hash_builder` is normally randomly generated, and is designed to allow HashMaps
    /// to be resistant to attacks that cause many collisions and very poor performance. Setting it
    /// manually using this function can expose a DoS attack vector.
    ///
    /// # Examples
    /// ```
    /// use std::collections::hash_map::RandomState;
    /// use countmap::CountMap;
    ///
    /// let s = RandomState::new();
    /// let mut map = CountMap::with_hasher(s);
    /// map.insert_or_increment("foo");
    /// ```
    pub fn with_hasher(hash_builder: S) -> Self {
        Self { map: HashMap::with_hasher(hash_builder) }
    }

    /// Creates an empty `CountMap` with the specified capacity, using hash_builder to hash the
    /// keys.
    ///
    /// The count map will be able to hold at least `capacity` elements without reallocating. If
    /// `capacity` is 0, the hash map will not allocate.
    ///
    /// Warning: `hash_builder` is normally randomly generated, and is designed to allow HashMaps
    /// to be resistant to attacks that cause many collisions and very poor performance. Setting it
    /// manually using this function can expose a DoS attack vector.
    ///
    /// # Examples
    /// ```
    /// use std::collections::hash_map::RandomState;
    /// use countmap::CountMap;
    ///
    /// let s = RandomState::new();
    /// let mut map = CountMap::with_capacity_and_hasher(10, s);
    /// map.insert_or_increment("foo");
    /// ```
    pub fn with_capacity_and_hasher(capacity: usize, hash_builder: S) -> Self {
        Self { map: HashMap::with_capacity_and_hasher(capacity, hash_builder) }
    }

    /// Returns a reference to the map's `BuildHasher`.
    pub fn hasher(&self) -> &S {
        self.map.hasher()
    }

    /// Returns the number of elements the map can hold without reallocating.
    ///
    /// This number is a lower bound; the `CountMap<K>` might be able to hold more, but is
    /// guaranteed to be able to hold at least this many.
    ///
    /// # Examples
    /// ```
    /// use countmap::CountMap;
    ///
    /// let map: CountMap<&str> = CountMap::with_capacity(100);
    /// assert!(map.capacity() >= 100);
    /// ```
    pub fn capacity(&self) -> usize {
        self.map.capacity()
    }

    /// Reserves capacity for at least `additional` more elements to be inserted in the `CountMap`.
    /// The collection ma reserve more space to avoid frequent reallocations.
    ///
    /// # Panics
    /// Panics if the new allocation size overflows usize.
    ///
    /// # Examples
    /// ```
    /// use countmap::CountMap;
    ///
    /// let mut map: CountMap<&str> = CountMap::with_capacity(5);
    /// map.reserve(10);
    /// assert!(map.capacity() >= 15);
    /// ```
    pub fn reserve(&mut self, additional: usize) {
        self.map.reserve(additional)
    }

    /// Shrinks the capacity of the map as much as possible. It will drop down as much as possible
    /// while maintaining the internal rules and possibly leaving some space in accordance with the
    /// resize policy.
    ///
    /// # Examples
    /// ```
    /// use countmap::CountMap;
    ///
    /// let mut map = CountMap::with_capacity(100);
    /// map.insert_or_increment("foo");
    /// map.insert_or_increment("bar");
    /// assert!(map.capacity() >= 100);
    /// map.shrink_to_fit();
    /// assert!(map.capacity() >= 2);
    /// ```
    pub fn shrink_to_fit(&mut self) {
        self.map.shrink_to_fit()
    }

    /// An iterator visiting all keys in arbitrary order. The iterator element type is `&'a K`.
    ///
    /// # Examples
    /// ```
    /// use countmap::CountMap;
    ///
    /// let mut map = CountMap::new();
    /// map.insert_or_increment("foo");
    /// map.insert_or_increment("bar");
    /// map.insert_or_increment("foo");
    ///
    /// for key in map.keys() {
    ///     println!("{}", key);
    /// }
    /// ```
    pub fn keys(&self) -> Keys<K, u64> {
        self.map.keys()
    }

    /// An iterator visiting all values in arbitrary order. The iterator element type is `&'a V`.
    ///
    /// # Examples
    /// ```
    /// use countmap::CountMap;
    ///
    /// let mut map = CountMap::new();
    /// map.insert_or_increment("foo");
    /// map.insert_or_increment("bar");
    /// map.insert_or_increment("foo");
    ///
    /// for val in map.values() {
    ///     println!("{}", val);
    /// }
    /// ```
    pub fn values(&self) -> Values<K, u64> {
        self.map.values()
    }

    /// Inserts or increments an element in the `CountMap`. The new value of the counter is
    /// returned.
    ///
    /// # Examples
    /// ```
    /// use countmap::CountMap;
    ///
    /// let mut count_map: CountMap<&str> = CountMap::new();
    ///
    /// assert_eq!(count_map.insert_or_increment("foo"), 1);
    /// assert_eq!(count_map.insert_or_increment("foo"), 2);
    /// assert_eq!(count_map.insert_or_increment("bar"), 1);
    /// ```
    pub fn insert_or_increment(&mut self, element: K) -> u64 {
        let count = self.map.entry(element).or_insert(0);
        *count += 1;
        *count
    }

    /// Increments an existing element in the `CountMap`. Returns an `Option` with the new value of
    /// the counter or `None` if the element doesn't exist.
    ///
    /// # Examples
    /// ```
    /// use countmap::CountMap;
    ///
    /// let mut count_map: CountMap<&str> = CountMap::new();
    ///
    /// assert_eq!(count_map.increment(&"foo"), None);
    ///
    /// count_map.insert_or_increment(&"foo");
    ///
    /// assert_eq!(count_map.increment(&"foo"), Some(2));
    /// ```
    pub fn increment(&mut self, element: &K) -> Option<u64> {
        let entry = self.map.get_mut(element);
        match entry {
            Some(count) => {
                *count += 1;
                Some(*count)
            }
            None => None,
        }
    }

    /// Returns an `Option` containing the current counter value of the specified element or
    /// `None`.
    ///
    /// # Examples
    /// ```
    /// use countmap::CountMap;
    ///
    /// let mut count_map: CountMap<&str> = CountMap::new();
    ///
    /// count_map.insert_or_increment("foo");
    ///
    /// assert_eq!(count_map.get_count(&"foo"), Some(1));
    /// assert_eq!(count_map.get_count(&"bar"), None);
    /// ```
    pub fn get_count(&self, element: &K) -> Option<u64> {
        self.map.get(element).cloned()
    }

    /// An iterator visiting all key-value pairs in arbitrary order. The iterator element type is
    /// (&'a K, &'a u64).
    ///
    /// # Examples
    /// ```
    /// use countmap::CountMap;
    ///
    /// let mut map = CountMap::new();
    ///
    /// map.insert_or_increment("foo");
    /// map.insert_or_increment("foo");
    /// map.insert_or_increment("bar");
    ///
    /// for (key, count) in map {
    ///     println!("key: {}, count: {}", key, count);
    /// }
    /// ```
    pub fn iter(&self) -> Iter<K, u64> {
        self.map.iter()
    }

    /// An iterator visiting all key-value pairs in arbitrary order, with mutable references to the
    /// values. The iterator element type is (&'a K, &'a mut V).
    ///
    /// # Examples
    /// ```
    /// use countmap::CountMap;
    ///
    /// let mut map = CountMap::new();
    ///
    /// map.insert_or_increment("foo");
    /// map.insert_or_increment("foo");
    /// map.insert_or_increment("bar");
    ///
    /// for (_, count) in map.iter_mut() {
    ///     *count += 3;
    /// }
    ///
    /// assert_eq!(map.get_count(&"foo"), Some(5));
    /// assert_eq!(map.get_count(&"bar"), Some(4));
    /// ```
    pub fn iter_mut(&mut self) -> IterMut<K, u64> {
        self.map.iter_mut()
    }

    /// Returns the number of elements in the map.
    ///
    /// # Examples
    /// ```
    /// use countmap::CountMap;
    ///
    /// let mut map = CountMap::new();
    /// assert_eq!(map.len(), 0);
    /// map.insert_or_increment("foo");
    /// assert_eq!(map.len(), 1);
    /// ```
    pub fn len(&self) -> usize {
        self.map.len()
    }

    /// Returns true if the map contains no elements.
    ///
    /// # Examples
    /// ```
    /// use countmap::CountMap;
    ///
    /// let mut map = CountMap::new();
    /// assert_eq!(map.is_empty(), true);
    /// map.insert_or_increment("foo");
    /// assert_eq!(map.is_empty(), false);
    /// ```
    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    /// Clears the map, returning all key-value pairs as an iterator. Keeps the allocated memory
    /// for reuse.
    ///
    /// # Examples
    /// ```
    /// use countmap::CountMap;
    ///
    /// let mut map = CountMap::new();
    /// map.insert_or_increment("foo");
    /// map.insert_or_increment("bar");
    ///
    /// for (k, c) in map.drain().take(1) {
    ///     assert!(k == "foo" || k == "bar");
    ///     assert_eq!(c, 1);
    /// }
    ///
    /// assert!(map.is_empty());
    /// ```
    pub fn drain(&mut self) -> Drain<K, u64> {
        self.map.drain()
    }

    /// Clears the map, removing all key-counter pairs. Keeps the allocated memory for reuse.
    ///
    /// # Examples
    /// ```
    /// use countmap::CountMap;
    ///
    /// let mut map = CountMap::new();
    /// map.insert_or_increment("foo");
    /// map.clear();
    /// assert!(map.is_empty())
    /// ```
    pub fn clear(&mut self) {
        self.map.clear()
    }

    /// Returns true if the map contains a value for the specified key.
    ///
    /// # Examples
    /// ```
    /// use countmap::CountMap;
    ///
    /// let mut map = CountMap::new();
    /// map.insert_or_increment("foo");
    /// assert!(map.contains_key(&"foo"));
    /// assert!(!map.contains_key(&"bar"));
    /// ```
    pub fn contains_key(&self, k: &K) -> bool {
        self.map.contains_key(k)
    }

    /// Removes a key from the map, returning the value at the key if the key was previously in the
    /// map.
    ///
    /// # Examples
    /// ```
    /// use countmap::CountMap;
    ///
    /// let mut map = CountMap::new();
    /// map.insert_or_increment("foo");
    /// assert_eq!(map.remove(&"foo"), Some(1));
    /// assert_eq!(map.remove(&"bar"), None);
    /// ```
    pub fn remove(&mut self, k: &K) -> Option<u64> {
        self.map.remove(k)
    }

    /// Retains only the elements specified by the predicate.
    ///
    /// In other words, remove all pairs `(k, v)` such that `f(&k,&mut v)` returns `false`.
    ///
    /// # Examples
    /// ```
    /// use countmap::CountMap;
    ///
    /// let mut map = CountMap::new();
    /// map.insert_or_increment("foo");
    /// map.insert_or_increment("foo");
    /// map.insert_or_increment("foo");
    /// map.insert_or_increment("bar");
    ///
    /// map.retain(|_, c| *c == 3);
    /// assert_eq!(map.len(), 1);
    /// ```
    pub fn retain<F>(&mut self, f: F)
    where
        F: FnMut(&K, &mut u64) -> bool,
    {
        self.map.retain(f)
    }
}

impl<K> Default for CountMap<K>
where
    K: Eq + Hash,
{
    fn default() -> Self {
        Self { map: HashMap::new() }
    }
}

impl<K> PartialEq for CountMap<K>
where
    K: Eq + Hash,
{
    fn eq(&self, other: &CountMap<K>) -> bool {
        self.map == other.map
    }
}

impl<K> Eq for CountMap<K>
where
    K: Eq + Hash,
{
}

impl<'a, K> IntoIterator for &'a CountMap<K>
where
    K: Eq + Hash,
{
    type Item = (&'a K, &'a u64);
    type IntoIter = Iter<'a, K, u64>;

    fn into_iter(self) -> Self::IntoIter {
        self.map.iter()
    }
}

impl<'a, K> IntoIterator for &'a mut CountMap<K>
where
    K: Eq + Hash,
{
    type Item = (&'a K, &'a mut u64);
    type IntoIter = IterMut<'a, K, u64>;

    fn into_iter(self) -> Self::IntoIter {
        self.map.iter_mut()
    }
}

impl<'a, K> IntoIterator for CountMap<K>
where
    K: Eq + Hash,
{
    type Item = (K, u64);
    type IntoIter = IntoIter<K, u64>;

    fn into_iter(self) -> Self::IntoIter {
        self.map.into_iter()
    }
}

impl<'a, K, Q> Index<&'a Q> for CountMap<K>
where
    K: Eq + Hash + Borrow<Q>,
    Q: ?Sized + Eq + Hash,
{
    type Output = u64;

    /// # Examples
    /// ```
    /// use countmap::CountMap;
    ///
    /// let mut map = CountMap::new();
    ///
    /// map.insert_or_increment("foo");
    /// assert_eq!(map["foo"], 1);
    /// ```
    fn index(&self, index: &Q) -> &Self::Output {
        &self.map[index]
    }
}

impl<K> FromIterator<(K, u64)> for CountMap<K>
where
    K: Eq + Hash,
{
    fn from_iter<T>(iter: T) -> Self
    where
        T: IntoIterator<Item = (K, u64)>,
    {
        Self { map: HashMap::from_iter(iter) }
    }
}

impl<K> Extend<(K, u64)> for CountMap<K>
where
    K: Eq + Hash,
{
    fn extend<T>(&mut self, iter: T)
    where
        T: IntoIterator<Item = (K, u64)>,
    {
        self.map.extend(iter)
    }
}

impl<'a, K> Extend<(&'a K, &'a u64)> for CountMap<K>
where
    K: 'a + Eq + Hash + Copy,
{
    fn extend<T>(&mut self, iter: T)
    where
        T: IntoIterator<Item = (&'a K, &'a u64)>,
    {
        self.map.extend(iter)
    }
}
