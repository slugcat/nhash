// TODO IdentityHashMap did not cope with huge size in the way that HashMap did.  So do something to make this cope with huge size.  I wonder why tree node was used instead of sub hash tables.  If HashMap and IdentityMap were proper for small or large sizes why would they not be proper for sub-hashes?  The answer seems to be that using trees copes with poorly distributed hashCodes.
/*
 * Copyright (c) 2000, 2022, Oracle and/or its affiliates. All rights reserved.
 * DO NOT ALTER OR REMOVE COPYRIGHT NOTICES OR THIS FILE HEADER.
 *
 * This code is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License version 2 only, as
 * published by the Free Software Foundation.  Oracle designates this
 * particular file as subject to the "Classpath" exception as provided
 * by Oracle in the LICENSE file that accompanied this code.
 *
 * This code is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
 * version 2 for more details (a copy is included in the LICENSE file that
 * accompanied this code).
 *
 * You should have received a copy of the GNU General Public License version
 * 2 along with this work; if not, write to the Free Software Foundation,
 * Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301 USA.
 *
 * Please contact Oracle, 500 Oracle Parkway, Redwood Shores, CA 94065 USA
 * or visit www.oracle.com if you need additional information or have any
 * questions.
 */

package newhash;

import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.lang.reflect.Array;
import java.util.*;
import java.util.function.BiConsumer;
import java.util.function.BiFunction;
import java.util.function.Consumer;

// TODO almost none of the javadoc has been updated.  Mostly it should look like HashMap's
/**
 * This class implements the {@code Map} interface with a hash table, using
 * reference-equality in place of object-equality when comparing keys (and
 * values).  In other words, in an {@code HashKeyHashMap}, two keys
 * {@code k1} and {@code k2} are considered equal if and only if
 * {@code (k1==k2)}.  (In normal {@code Map} implementations (like
 * {@code HashMap}) two keys {@code k1} and {@code k2} are considered equal
 * if and only if {@code (k1==null ? k2==null : k1.equals(k2))}.)
 *
 * <p><b>This class is <i>not</i> a general-purpose {@code Map}
 * implementation!  While this class implements the {@code Map} interface, it
 * intentionally violates {@code Map's} general contract, which mandates the
 * use of the {@code equals} method when comparing objects.  This class is
 * designed for use only in the rare cases wherein reference-equality
 * semantics are required.</b>
 *
 * <p>The view collections of this map also have reference-equality semantics
 * for their elements. See the {@link Map#keySet() keySet}, {@link Map#values() values},
 * and {@link Map#entrySet() entrySet} methods for further information.
 *
 * <p>A typical use of this class is <i>topology-preserving object graph
 * transformations</i>, such as serialization or deep-copying.  To perform such
 * a transformation, a program must maintain a "node table" that keeps track
 * of all the object references that have already been processed.  The node
 * table must not equate distinct objects even if they happen to be equal.
 * Another typical use of this class is to maintain <i>proxy objects</i>.  For
 * example, a debugging facility might wish to maintain a proxy object for
 * each object in the program being debugged.
 *
 * <p>This class provides all of the optional map operations, and permits
 * {@code null} values and the {@code null} key.  This class makes no
 * guarantees as to the order of the map; in particular, it does not guarantee
 * that the order will remain constant over time.
 *
 * <p>This class provides constant-time performance for the basic
 * operations ({@code get} and {@code put}), assuming the system
 * identity hash function ({@link System#identityHashCode(Object)})
 * disperses elements properly among the buckets.
 *
 * <p>This class has one tuning parameter (which affects performance but not
 * semantics): <i>expected maximum size</i>.  This parameter is the maximum
 * number of key-value mappings that the map is expected to hold.  Internally,
 * this parameter is used to determine the number of buckets initially
 * comprising the hash table.  The precise relationship between the expected
 * maximum size and the number of buckets is unspecified.
 *
 * <p>If the size of the map (the number of key-value mappings) sufficiently
 * exceeds the expected maximum size, the number of buckets is increased.
 * Increasing the number of buckets ("rehashing") may be fairly expensive, so
 * it pays to create identity hash maps with a sufficiently large expected
 * maximum size.  On the other hand, iteration over collection views requires
 * time proportional to the number of buckets in the hash table, so it
 * pays not to set the expected maximum size too high if you are especially
 * concerned with iteration performance or memory usage.
 *
 * <p><strong>Note that this implementation is not synchronized.</strong>
 * If multiple threads access an identity hash map concurrently, and at
 * least one of the threads modifies the map structurally, it <i>must</i>
 * be synchronized externally.  (A structural modification is any operation
 * that adds or deletes one or more mappings; merely changing the value
 * associated with a key that an instance already contains is not a
 * structural modification.)  This is typically accomplished by
 * synchronizing on some object that naturally encapsulates the map.
 *
 * If no such object exists, the map should be "wrapped" using the
 * {@link Collections#synchronizedMap Collections.synchronizedMap}
 * method.  This is best done at creation time, to prevent accidental
 * unsynchronized access to the map:<pre>
 *   Map m = Collections.synchronizedMap(new HashKeyHashMap(...));</pre>
 *
 * <p>The iterators returned by the {@code iterator} method of the
 * collections returned by all of this class's "collection view
 * methods" are <i>fail-fast</i>: if the map is structurally modified
 * at any time after the iterator is created, in any way except
 * through the iterator's own {@code remove} method, the iterator
 * will throw a {@link ConcurrentModificationException}.  Thus, in the
 * face of concurrent modification, the iterator fails quickly and
 * cleanly, rather than risking arbitrary, non-deterministic behavior
 * at an undetermined time in the future.
 *
 * <p>Note that the fail-fast behavior of an iterator cannot be guaranteed
 * as it is, generally speaking, impossible to make any hard guarantees in the
 * presence of unsynchronized concurrent modification.  Fail-fast iterators
 * throw {@code ConcurrentModificationException} on a best-effort basis.
 * Therefore, it would be wrong to write a program that depended on this
 * exception for its correctness: <i>fail-fast iterators should be used only
 * to detect bugs.</i>
 *
 * <p>This class is a member of the
 * <a href="{@docRoot}/java.base/java/util/package-summary.html#CollectionsFramework">
 * Java Collections Framework</a>.
 *
 * @implNote
 * TODO write up implementation
 * <p>This is a simple <i>linear-probe</i> hash table,
 * as described for example in texts by Sedgewick and Knuth.  The array
 * contains alternating keys and values, with keys at even indexes and values
 * at odd indexes. (This arrangement has better locality for large
 * tables than does using separate arrays.)  For many Java implementations
 * and operation mixes, this class will yield better performance than
 * {@link HashMap}, which uses <i>chaining</i> rather than linear-probing.
 *
 * @param <K> the type of keys maintained by this map
 * @param <V> the type of mapped values
 *
 * @see     System#identityHashCode(Object)
 * @see     Object#hashCode()
 * @see     Collection
 * @see     Map
 * @see     HashMap
 * @see     TreeMap
 * @author  Doug Lea and Josh Bloch
 * @author  David Witten
 * @since   1.4
 */

/**
FUTURE TODO
<ul>
<li>Array sizing</li>
I don't quite see why IdentityHashMap uses 2^x sizes since it must move, I think more than 1/2 of the items
would not go in the same slot on each growth.  Even if there is a good reason for this for IdentityHashMap, I think it would apply
less to this, since all that hashes are readily available.  So there is a fair chance that using prime sizes will be more
useful since it will reduce the chance of collisions.  Consider constructing a table of primes.  One approach would be to have twice as many primes for the range [2^(x+1), 2^(x+2)] as their is for the range [2^(x), 2^(x+1)].  In this way the larger hash-tables would consume (a lot) less unused space.  OTOH smaller tables will be more frequent so having a lots of primes for them to choose from seems useful as well.
Finding the immediately larger prime for a wanted size would be done by a binary search.  However this binary search would not need to start in the middle.  It should be possible to guess a good starting probe.  If it is too small then the next probe would be at 1.5 (or 2?) * currentProbeIndex.

For larger tables it is worth considering having the first hash table include the index into an array of the keys and values.  Since this would mean that the keys and values array on resize could just be copied directly to the new/larger array.  If we had such a scheme it may be that holes caused by deletions could be recorded by having the index (in the hash-table) to the array of keys+values be the negative (ie sentinel) value of the index of the next hole.  The index of the 1st hole would be stored in the HashMap Object.

Do this as a separate commit and benchmark it separately.

<li>try implementation that uses non-nullable value objects.  Each would have hashkey, key, value</li>
<li>have factory method that would different implementations, based on context.  Eg whether compressed pointers are being used (old version of hashmap may be better for this).</li>

<li>Do immutable versions
 Immutable versions
 <ul>have hash-key map have key and index into a simple array of key-value. This will make iterating much faster.</ul>
 <ul>Maybe Use bytes and shorts for hashkey-map if number of elements is much less than 2^7, 2^15.  Main benefit would be very few cache misses</ul>
</li>
 <li> A less restrictive option than full immutability, are Maps which the developer knows won't be accessed while new entries are being added.  In the approach where there are two arrays (an open hashing one, and an array holding the keys&values) this would allow just adding to the K&v one and updating the hashing one at the end to reduce the amount of time spent doubling the open hashing one.  Even the k&v one would not need to be increased in size as the new elements could be added to some temporary data structure (like a rope) while it is being built.
 </li>
 <li>I think it would be fairly easy to isolate the difference between the one and two table approaches by changing the KeyhashKeyValue to hide all the differences.  Can maybe write it to use subclassing but also be implemented by a macro pre-processor.</li>
<li>do hashset
 this will allow the second table to just have the list of values.  Constructor would take parameters for equals() and hashcode(); in this way the hash table would act like an index of a SQL table.  That is there could be multiple different indexes for the same set of data.
</li>
 <li>use non-nullable value objects.  Then the 1st table could have integer hashkey and pointer to element (or if collision (linked?) list of elements).  </li>

 <li>Look to see what has already been done in the (immutable) hashmap, hashset space</li>

 </ul>

 */

/*

Possible approaches:

1. array of hash codes, (index*2 corresponding) to key and value.  When multiple keys have the
same hash then the key will be an instance of

2. array of hash codes, key and value.  PROBLEM: unless the currently available jvm will can
store integer and reference contiguously this won't work.  It is expected this won't work until
at least the can't-be-null JEP is previewed.


 */

public class HashKeyValueHashMap<K,V> extends AbstractMap<K,V>
    implements Map<K,V>, java.io.Serializable, Cloneable
{
  /**
   * The initial capacity used by the no-args constructor.
   * MUST be a power of two.  The value 32 corresponds to the
   * (specified) expected maximum size of 21, given a load factor
   * of 2/3.
   */
  private static final int DEFAULT_CAPACITY = 32;

  /**
   * The minimum capacity, used if a lower value is implicitly specified
   * by either of the constructors with arguments.  The value 4 corresponds
   * to an expected maximum size of 2, given a load factor of 2/3.
   * MUST be a power of two.
   */
  private static final int MINIMUM_CAPACITY = 4;

  /**
   * The maximum capacity, used if a higher value is implicitly specified
   * by either of the constructors with arguments.
   * MUST be a power of two <= 1<<29.
   *
   * In fact, the map can hold no more than MAXIMUM_CAPACITY-1 items
   * because it has to have at least one slot with the key == null
   * in order to avoid infinite loops in get(), put(), remove()
   */
  private static final int MAXIMUM_CAPACITY = 1 << 29;

  /**
   * The table, resized as necessary. Length MUST always be a power of two.
   */
  transient MaskedHashKeyValue/*TODO make null-free: !*/[] table; // non-private to simplify nested class access
  /**
   * A linear-probe hash table containing only hashes of keys.  A hashed key at index X will
   * have a matching key at
   * <tt>2X</tt>, and matching value at <tt>2X+1</tt>.   The idea of this class is to use
   * <tt>hashedKeyTable</tt> to quickly find the index in <tt>table</tt>.  It is hoped that this
   * will be faster than a normal HashMap because a typical level 1 cpu cache cache-line fetch
   * will allow the linear probing to check 16 hashKeys, and if that does not suffice cpu
   * prefetching will grab the next cache-line all because there is no object dereferencing.
   * Resized as necessary. Length MUST always be a power of two.
   */

  /**
   * The number of key-value mappings contained in this identity hash map.
   *
   * @serial
   */
  int size;

  /**
   * The number of modifications, to support fast-fail iterators
   */
  transient int modCount;

  /**
   * Value representing null keys inside tables.
   */
  static final Object NULL_KEY = new String("NullKey");

  /**
   * Use NULL_KEY for key if it is null.
   */
  private static Object maskNull(Object key) {
    return (key == null ? NULL_KEY : key);
  }

  /**
   * Returns internal representation of null key back to caller as null.
   */
  static Object unmaskNull(Object key) {
    return (key == NULL_KEY ? null : key);
  }

  static int itemUnmaskedKeyHash(MaskedHashKeyValue item) {
    return item.key == NULL_KEY ? 0 : item.maskedHash;
  }

  /**
   * Constructs a new, empty identity hash map with a default expected
   * maximum size (21).
   */
  public HashKeyValueHashMap() {
    init(DEFAULT_CAPACITY);
  }

  /**
   * Constructs a new, empty map with the specified expected maximum size.
   * Putting more than the expected number of key-value mappings into
   * the map may cause the internal data structure to grow, which may be
   * somewhat time-consuming.
   *
   * @param expectedMaxSize the expected maximum size of the map
   * @throws IllegalArgumentException if {@code expectedMaxSize} is negative
   */
  public HashKeyValueHashMap(int expectedMaxSize) {
    if (expectedMaxSize < 0)
      throw new IllegalArgumentException("expectedMaxSize is negative: "
          + expectedMaxSize);
    init(capacity(expectedMaxSize));
  }

  /**
   * Returns the appropriate capacity for the given expected maximum size.
   * Returns the smallest power of two between MINIMUM_CAPACITY and
   * MAXIMUM_CAPACITY, inclusive, that is greater than (3 *
   * expectedMaxSize)/2, if such a number exists.  Otherwise returns
   * MAXIMUM_CAPACITY.
   */
  private static int capacity(int expectedMaxSize) {
    // assert expectedMaxSize >= 0;
    return
        (expectedMaxSize > MAXIMUM_CAPACITY / 3) ? MAXIMUM_CAPACITY :
            (expectedMaxSize <= 2 * MINIMUM_CAPACITY / 3) ? MINIMUM_CAPACITY :
                Integer.highestOneBit(expectedMaxSize + (expectedMaxSize << 1));
  }

  /**
   * Initializes object to be an empty map with the specified initial
   * capacity, which is assumed to be a power of two between
   * MINIMUM_CAPACITY and MAXIMUM_CAPACITY inclusive.
   */
  private void init(int initCapacity) {
    // assert (initCapacity & -initCapacity) == initCapacity; // power of 2
    // assert initCapacity >= MINIMUM_CAPACITY;
    // assert initCapacity <= MAXIMUM_CAPACITY;

    table = new MaskedHashKeyValue[initCapacity];
  }

  /**
   * Constructs a new identity hash map containing the keys-value mappings
   * in the specified map.
   *
   * @param m the map whose mappings are to be placed into this map
   * @throws NullPointerException if the specified map is null
   */
  public HashKeyValueHashMap(Map<? extends K, ? extends V> m) {
    // Allow for a bit of growth
    this((int) ((1 + m.size()) * 1.1));
    putAll(m);
  }

  /**
   * Returns the number of key-value mappings in this identity hash map.
   *
   * @return the number of key-value mappings in this map
   */
  public int size() {
    return size;
  }

  /**
   * Returns {@code true} if this identity hash map contains no key-value
   * mappings.
   *
   * @return {@code true} if this identity hash map contains no key-value
   *         mappings
   */
  public boolean isEmpty() {
    return size == 0;
  }

  /**
   * Returns index for Object x.
   */
  static int getIndex(int hashCode, int length) {
    return (hashCode ^ (hashCode >>> 16)) & (length - 1);
  }

  /**
   * Circularly traverses table of size len.
   */
  private static int nextKeyIndex(int i, int len) {
    return (i + 1 < len ? i + 1 : 0);
  }

  /**
   * Returns the value to which the specified key is mapped,
   * or {@code null} if this map contains no mapping for the key.
   *
   * <p>More formally, if this map contains a mapping from a key
   * {@code k} to a value {@code v} such that {@code (key == k)},
   * then this method returns {@code v}; otherwise it returns
   * {@code null}.  (There can be at most one such mapping.)
   *
   * <p>A return value of {@code null} does not <i>necessarily</i>
   * indicate that the map contains no mapping for the key; it's also
   * possible that the map explicitly maps the key to {@code null}.
   * The {@link #containsKey containsKey} operation may be used to
   * distinguish these two cases.
   *
   * @see #put(Object, Object)
   */
  @SuppressWarnings("unchecked")
  public V get(Object key) {
    Object k = maskNull(key);
    final int hash = k.hashCode();
    MaskedHashKeyValue[] tab = table;
    int len = tab.length;
    int i = getIndex(hash, len);
    while (true) {
      MaskedHashKeyValue item = tab[i];
      if (item.maskedHash == hash && item.key.equals(k))
        return (V) item.value;
      if (item.key == null)
        return null;
      i = nextKeyIndex(i, len);
    }
  }

  /**
   * Tests whether the specified object reference is a key in this identity
   * hash map. Returns {@code true} if and only if this map contains a mapping
   * with key {@code k} such that {@code (key == k)}.
   *
   * @param   key   possible key
   * @return  {@code true} if the specified object reference is a key
   *          in this map
   * @see     #containsValue(Object)
   */
  // TODO look at all occurrences of Objects.equals.  Should probably only be used for values
  public boolean containsKey(Object key) {
    Object k = maskNull(key);
    final int hash = k.hashCode();
    MaskedHashKeyValue[] tab = table;
    int len = tab.length;
    int i = getIndex(hash, len);
    while (true) {
      MaskedHashKeyValue item = tab[i];
      if (item.maskedHash == hash && item.key.equals(k))
        return true;
      if (item.key == null)
        return false;
      i = nextKeyIndex(i, len);
    }
  }

  /**
   * Tests whether the specified object reference is a value in this identity
   * hash map. Returns {@code true} if and only if this map contains a mapping
   * with value {@code v} such that {@code (value == v)}.
   *
   * @param value value whose presence in this map is to be tested
   * @return {@code true} if this map maps one or more keys to the
   *         specified object reference
   * @see     #containsKey(Object)
   */
  public boolean containsValue(Object value) {
    MaskedHashKeyValue[] tab = table;
    for (int i = 1; i < tab.length; i++) {
      MaskedHashKeyValue item = tab[i];
      if (item.value == value && item.key != null)
        return true;
    }

    return false;
  }

  /**
   * Tests if the specified key-value mapping is in the map.
   *
   * @param   key   possible key
   * @param   value possible value
   * @return  {@code true} if and only if the specified key-value
   *          mapping is in the map
   */
  private boolean containsMapping(Object key, Object value) {
    Object k = maskNull(key);
    final int hash = k.hashCode();
    MaskedHashKeyValue[] tab = table;
    int len = tab.length;
    int i = getIndex(hash, len);
    while (true) {
      MaskedHashKeyValue item = tab[i];
      if (item.maskedHash == hash && item.key.equals(k))
        return item.value == value;
      if (item.key == null)
        return false;
      i = nextKeyIndex(i, len);
    }
  }

  /**
   * Associates the specified value with the specified key in this identity
   * hash map. If this map already {@link Map#containsKey(Object) contains}
   * a mapping for the key, the old value is replaced, otherwise, a new mapping
   * is inserted into this map.
   *
   * @param key the key with which the specified value is to be associated
   * @param value the value to be associated with the specified key
   * @return the previous value associated with {@code key}, or
   *         {@code null} if there was no mapping for {@code key}.
   *         (A {@code null} return can also indicate that the map
   *         previously associated {@code null} with {@code key}.)
   * @see     Object#equals(Object)
   * @see     #get(Object)
   * @see     #containsKey(Object)
   */
  public V put(K key, V value) {
    final Object k = maskNull(key);
    final int hash = k.hashCode();

    retryAfterResize: for (;;) {
      final MaskedHashKeyValue/*TODO make null-restricted using ! everywhere*/[] tab = table;
      final int len = tab.length;
      int i = getIndex(hash, len);

      for (MaskedHashKeyValue item; (item = tab[i]).key != null;
           i = nextKeyIndex(i, len)) {
        if (item.maskedHash == hash && item.key.equals(k)) {
          @SuppressWarnings("unchecked")
          V oldValue = (V) tab[i].value;
          tab[i] = new MaskedHashKeyValue(hash, k, value);
          return oldValue;
        }
      }

      final int s = size + 1;
      // Use optimized form of 3 * s.
      // Next capacity is len, 2 * current capacity.
      if (s + (s << 1) > len && resize(len))
        continue retryAfterResize;

      modCount++;
      tab[i] = new MaskedHashKeyValue(hash, k, value);
      size = s;
      return null;
    }
  }

  /**
   * Resizes the table if necessary to hold given capacity.
   *
   * @param newCapacity the new capacity, must be a power of two.
   * @return whether a resize did in fact take place
   */
  private boolean resize(int newCapacity) {
    // assert (newCapacity & -newCapacity) == newCapacity; // power of 2
    int newLength = newCapacity * 2;

    MaskedHashKeyValue[] oldTable = table;
    int oldLength = oldTable.length;
    if (oldLength == 2 * MAXIMUM_CAPACITY) { // can't expand any further
      if (size == MAXIMUM_CAPACITY - 1)
        throw new IllegalStateException("Capacity exhausted.");
      return false;
    }
    if (oldLength >= newLength)
      return false;

    MaskedHashKeyValue[] newTable = new MaskedHashKeyValue[newLength];

    for (int j = 0; j < oldLength; j += 2) {
      MaskedHashKeyValue oldElem = oldTable[j];
      if (oldElem.key != null) {
        oldTable[j] = MaskedHashKeyValue.EMPTY;
        int i = getIndex(oldElem.maskedHash, newLength);
        while (newTable[i] != null)
          i = nextKeyIndex(i, newLength);
        newTable[i] = oldElem;
      }
    }
    table = newTable;
    return true;
  }

  /**
   * Copies all of the mappings from the specified map to this map.
   * For each mapping in the specified map, if this map already
   * {@link Map#containsKey(Object) contains} a mapping for the key,
   * its value is replaced with the value from the specified map;
   * otherwise, a new mapping is inserted into this map.
   *
   * @param m mappings to be stored in this map
   * @throws NullPointerException if the specified map is null
   */
  public void putAll(Map<? extends K, ? extends V> m) {
    int n = m.size();
    if (n == 0)
      return;
    if (n > size)
      resize(capacity(n)); // conservatively pre-expand

    // TODO optimize setting of hashKey if m is a HashKeyValueHashMap?
    for (Entry<? extends K, ? extends V> e : m.entrySet())
      put(e.getKey(), e.getValue());
  }

  // TODO fix comments.  Eg this was fixed to copy from HashMap and not use what was done for IdentityHashMap
  /**
   * Removes the mapping for the specified key from this map if present.
   *
   * @param  key key whose mapping is to be removed from the map
   * @return the previous value associated with {@code key}, or
   *         {@code null} if there was no mapping for {@code key}.
   *         (A {@code null} return can also indicate that the map
   *         previously associated {@code null} with {@code key}.)
   */
  public V remove(Object key) {
    Object k = maskNull(key);
    final int hash = k.hashCode();
    MaskedHashKeyValue[] tab = table;
    int len = tab.length;
    int i = getIndex(hash, len);

    while (true) {
      MaskedHashKeyValue item = tab[i];
      if (item.maskedHash == hash && item.key.equals(k)) {
        modCount++;
        size--;
        @SuppressWarnings("unchecked") V oldValue = (V) item.value;
        tab[i] = MaskedHashKeyValue.EMPTY;
        closeDeletion(i);
        return oldValue;
      }
      if (item.key == null)
        return null;
      i = nextKeyIndex(i, len);
    }
  }

  /**
   * Removes the specified key-value mapping from the map if it is present.
   *
   * @param   key   possible key
   * @param   value possible value
   * @return  {@code true} if and only if the specified key-value
   *          mapping was in the map
   */
  private boolean removeMapping(Object key, Object value) {
    Object k = maskNull(key);
    final int hash = k.hashCode();
    MaskedHashKeyValue[] tab = table;
    int len = tab.length;
    int i = getIndex(hash, len);

    while (true) {
      MaskedHashKeyValue item = tab[i];
      if (item.maskedHash == hash && item.key.equals(k)) {
        if (!Objects.equals(item.value, value))
          return false;
        modCount++;
        size--;
        tab[i] = MaskedHashKeyValue.EMPTY;
        closeDeletion(i);
        return true;
      }
      if (item.key == null)
        return false;
      i = nextKeyIndex(i, len);
    }
  }

  /**
   * Rehash all possibly-colliding entries following a
   * deletion. This preserves the linear-probe
   * collision properties required by get, put, etc.
   *
   * @param d the index of a newly empty deleted slot
   */
  private void closeDeletion(int d) {
    // Adapted from Knuth Section 6.4 Algorithm R
    MaskedHashKeyValue[] tab = table;
    int len = tab.length;

    // Look for items to swap into newly vacated slot
    // starting at index immediately following deletion,
    // and continuing until a null slot is seen, indicating
    // the end of a run of possibly-colliding keys.
    MaskedHashKeyValue item;
    for (int i = nextKeyIndex(d, len); (item = tab[i]).key != null; i = nextKeyIndex(i, len)) {
      // The following test triggers if the item at slot i (which
      // hashes to be at slot r) should take the spot vacated by d.
      // If so, we swap it in, and then continue with d now at the
      // newly vacated i.  This process will terminate when we hit
      // the null slot at the end of this run.
      // The test is messy because we are using a circular table.
      int hash = item.maskedHash;
      int r = getIndex(hash, len);
      if ((i < r && (r <= d || d <= i)) || (r <= d && d <= i)) {
        tab[d] = tab[i];
        tab[i] = MaskedHashKeyValue.EMPTY;
        d = i;
      }
    }
  }

  /**
   * Removes all of the mappings from this map.
   * The map will be empty after this call returns.
   */
  public void clear() {
    modCount++;
    MaskedHashKeyValue[] tab = table;
    for (int i = 0; i < tab.length; i++) // TODO replace with Arrays.fill() if that works with primitive
      tab[i] = MaskedHashKeyValue.EMPTY;
    size = 0;
  }

  /**
   * Compares the specified object with this map for equality.  Returns
   * {@code true} if the given object is also a map and the two maps
   * represent identical object-reference mappings.  More formally, this
   * map is equal to another map {@code m} if and only if
   * {@code this.entrySet().equals(m.entrySet())}. See the
   * {@link Map#entrySet() entrySet} method for the specification of equality
   * of this map's entries.
   *
   * <p><b>Owing to the reference-equality-based semantics of this map it is
   * possible that the symmetry and transitivity requirements of the
   * {@code Object.equals} contract may be violated if this map is compared
   * to a normal map.  However, the {@code Object.equals} contract is
   * guaranteed to hold among {@code HashKeyHashMap} instances.</b>
   *
   * @param  o object to be compared for equality with this map
   * @return {@code true} if the specified object is equal to this map
   * @see Object#equals(Object)
   */
  public boolean equals(Object o) {
    if (o == this) {
      return true;
    } else if (o instanceof HashKeyValueHashMap<?, ?> m) {
      if (m.size() != size)
        return false;

      MaskedHashKeyValue[] tab = m.table;
      for (int i = 0; i < tab.length; i++) {
        MaskedHashKeyValue item = tab[i];
        // TODO is it better to have a local variable copy of the item or just use tab[i]?
        if (item.key != null && !containsMapping(item.maskedHash, item.value))
          return false;
      }
      return true;
    } else if (o instanceof Map<?, ?> m) {
      return entrySet().equals(m.entrySet());
    } else {
      return false;  // o is not a Map
    }
  }

  /**
   * Returns the hash code value for this map.  The hash code of a map is
   * defined to be the sum of the hash codes of each entry in the map's
   * {@code entrySet()} view.  This ensures that {@code m1.equals(m2)}
   * implies that {@code m1.hashCode()==m2.hashCode()} for any two
   * {@code HashKeyHashMap} instances {@code m1} and {@code m2}, as
   * required by the general contract of {@link Object#hashCode}.
   *
   * <p><b>Owing to the reference-equality-based semantics of the
   * {@code Map.Entry} instances in the set returned by this map's
   * {@code entrySet} method, it is possible that the contractual
   * requirement of {@code Object.hashCode} mentioned in the previous
   * paragraph will be violated if one of the two objects being compared is
   * an {@code HashKeyHashMap} instance and the other is a normal map.</b>
   *
   * @return the hash code value for this map
   * @see Object#equals(Object)
   * @see #equals(Object)
   */
  public int hashCode() {
    int result = 0;
    MaskedHashKeyValue[] tab = table;
    for (int i = 0; i < tab.length; i++) {
      final MaskedHashKeyValue item = tab[i];
      if (item.key != null) {
        result += item.maskedHash ^ Objects.hashCode(item.value);
      }
    }
    return result;
  }

  /**
   * Returns a shallow copy of this identity hash map: the keys and values
   * themselves are not cloned.
   *
   * @return a shallow copy of this map
   */
  public Object clone() {
    try {
      HashKeyValueHashMap<?,?> m = (HashKeyValueHashMap<?,?>) super.clone();
      m.entrySet = null;
      m.table = table.clone();
      return m;
    } catch (CloneNotSupportedException e) {
      throw new InternalError(e);
    }
  }

  private abstract class HashKeyValueHashMapIterator<T> implements Iterator<T> {
    int index = (size != 0 ? 0 : table.length); // current slot.
    int expectedModCount = modCount; // to support fast-fail
    int lastReturnedIndex = -1;      // to allow remove()
    boolean indexValid; // To avoid unnecessary next computation
    MaskedHashKeyValue[] traversalTable = table; // reference to main table or copy

    public boolean hasNext() {
      MaskedHashKeyValue[] tab = traversalTable;
      for (int i = index; i < tab.length; i++) {
        Object key = tab[i].key;
        if (key != null) {
          index = i;
          return indexValid = true;
        }
      }
      index = tab.length;
      return false;
    }

    protected int nextIndex() {
      if (modCount != expectedModCount)
        throw new ConcurrentModificationException();
      if (!indexValid && !hasNext())
        throw new NoSuchElementException();

      indexValid = false;
      lastReturnedIndex = index;
      index++;
      return lastReturnedIndex;
    }

    public void remove() {
      if (lastReturnedIndex == -1)
        throw new IllegalStateException();
      if (modCount != expectedModCount)
        throw new ConcurrentModificationException();

      expectedModCount = ++modCount;
      int deletedSlot = lastReturnedIndex;
      lastReturnedIndex = -1;
      // back up index to revisit new contents after deletion
      index = deletedSlot;
      indexValid = false;

      // Removal code proceeds as in closeDeletion except that
      // it must catch the rare case where an element already
      // seen is swapped into a vacant slot that will be later
      // traversed by this iterator. We cannot allow future
      // next() calls to return it again.  The likelihood of
      // this occurring under 2/3 load factor is very slim, but
      // when it does happen, we must make a copy of the rest of
      // the table to use for the rest of the traversal. Since
      // this can only happen when we are near the end of the table,
      // even in these rare cases, this is not very expensive in
      // time or space.

      MaskedHashKeyValue[] tab = traversalTable;
      int len = tab.length;

      int d = deletedSlot;
      Object key = tab[d];
      tab[d] = MaskedHashKeyValue.EMPTY;

      // If traversing a copy, remove in real table.
      // We can skip gap-closure on copy.
      if (tab != HashKeyValueHashMap.this.table) {
        HashKeyValueHashMap.this.remove(key);
        expectedModCount = modCount;
        return;
      }

      size--;

      MaskedHashKeyValue item;
      for (int i = nextKeyIndex(d, len); (item = tab[i]).key != null; i = nextKeyIndex(i, len)) {
        int hash = item.maskedHash;
        int r = getIndex(hash, len);
        // See closeDeletion for explanation of this conditional
        if ((i < r && (r <= d || d <= i)) ||
            (r <= d && d <= i)) {

          // If we are about to swap an already-seen element
          // into a slot that may later be returned by next(),
          // then clone the rest of table for use in future
          // next() calls. It is OK that our copy will have
          // a gap in the "wrong" place, since it will never
          // be used for searching anyway.

          if (i < deletedSlot && d >= deletedSlot &&
              traversalTable == HashKeyValueHashMap.this.table) {
            int remaining = len - deletedSlot;
            MaskedHashKeyValue[] newTable = new MaskedHashKeyValue[remaining];
            System.arraycopy(tab, deletedSlot,
                newTable, 0, remaining);
            traversalTable = newTable;
            index = 0;
          }

          tab[d] = item;
          tab[i] = MaskedHashKeyValue.EMPTY;
          d = i;
        }
      }
    }
  }

  private class KeyIterator extends HashKeyValueHashMapIterator<K> {
    @SuppressWarnings("unchecked")
    public K next() {
      return (K) unmaskNull(traversalTable[nextIndex()].key);
    }
  }

  private class ValueIterator extends HashKeyValueHashMapIterator<V> {
    @SuppressWarnings("unchecked")
    public V next() {
      return (V) traversalTable[nextIndex()].value;
    }
  }

  private class EntryIterator
      extends HashKeyValueHashMapIterator<Entry<K,V>>
  {
    private Entry lastReturnedEntry;

    public Map.Entry<K,V> next() {
      lastReturnedEntry = new Entry(nextIndex());
      return lastReturnedEntry;
    }

    public void remove() {
      lastReturnedIndex =
          ((null == lastReturnedEntry) ? -1 : lastReturnedEntry.index);
      super.remove();
      lastReturnedEntry.index = lastReturnedIndex;
      lastReturnedEntry = null;
    }

    private class Entry implements Map.Entry<K,V> {
      private int index;

      private Entry(int index) {
        this.index = index;
      }

      @SuppressWarnings("unchecked")
      public K getKey() {
        checkIndexForEntryUse();
        return (K) unmaskNull(traversalTable[index].key);
      }

      @SuppressWarnings("unchecked")
      public V getValue() {
        checkIndexForEntryUse();
        return (V) traversalTable[index].value;
      }

      @SuppressWarnings("unchecked")
      public V setValue(V value) {
        checkIndexForEntryUse();
        final MaskedHashKeyValue item = traversalTable[index];
        V oldValue = (V) item.value;
        traversalTable[index] = new MaskedHashKeyValue(item.maskedHash, item.key, value);
        // if shadowing, force into main table
        if (traversalTable != HashKeyValueHashMap.this.table)
          put((K) traversalTable[index].key, value);
        return oldValue;
      }

      public boolean equals(Object o) {
        if (index < 0)
          return super.equals(o);

        return o instanceof Map.Entry<?, ?> e
            && Objects.equals(e.getKey(), unmaskNull(traversalTable[index].key))
            && Objects.equals(e.getValue(), traversalTable[index].value);
      }

      public int hashCode() {
        if (lastReturnedIndex < 0)
          return super.hashCode();

        final MaskedHashKeyValue item = traversalTable[index];
        return itemUnmaskedKeyHash(item) ^ Objects.hashCode(item.value);
      }

      public String toString() {
        if (index < 0)
          return super.toString();

        return (unmaskNull(traversalTable[index].key) + "="
            + traversalTable[index].value);
      }

      private void checkIndexForEntryUse() {
        if (index < 0)
          throw new IllegalStateException("Entry was removed");
      }
    }
  }

  // Views

  /**
   * This field is initialized to contain an instance of the entry set
   * view the first time this view is requested.  The view is stateless,
   * so there's no reason to create more than one.
   */
  private transient Set<Map.Entry<K,V>> entrySet;

  /**
   * Returns an identity-based set view of the keys contained in this map.
   * The set is backed by the map, so changes to the map are reflected in
   * the set, and vice-versa.  If the map is modified while an iteration
   * over the set is in progress, the results of the iteration are
   * undefined.  The set supports element removal, which removes the
   * corresponding mapping from the map, via the {@code Iterator.remove},
   * {@code Set.remove}, {@code removeAll}, {@code retainAll}, and
   * {@code clear} methods.  It does not support the {@code add} or
   * {@code addAll} methods.
   *
   * <p><b>While the object returned by this method implements the
   * {@code Set} interface, it does <i>not</i> obey {@code Set's} general
   * contract.  Like its backing map, the set returned by this method
   * defines element equality as reference-equality rather than
   * object-equality.  This affects the behavior of its {@code contains},
   * {@code remove}, {@code containsAll}, {@code equals}, and
   * {@code hashCode} methods.</b>
   *
   * <p><b>The {@code equals} method of the returned set returns {@code true}
   * only if the specified object is a set containing exactly the same
   * object references as the returned set.  The symmetry and transitivity
   * requirements of the {@code Object.equals} contract may be violated if
   * the set returned by this method is compared to a normal set.  However,
   * the {@code Object.equals} contract is guaranteed to hold among sets
   * returned by this method.</b>
   *
   * <p>The {@code hashCode} method of the returned set returns the sum of
   * the <i>identity hashcodes</i> of the elements in the set, rather than
   * the sum of their hashcodes.  This is mandated by the change in the
   * semantics of the {@code equals} method, in order to enforce the
   * general contract of the {@code Object.hashCode} method among sets
   * returned by this method.
   *
   * @return an identity-based set view of the keys contained in this map
   * @see Object#equals(Object)
   * @see System#identityHashCode(Object)
   */
  private Set<K> keySet; // TODO remove this if this class is moved to java.util
  public Set<K> keySet() {
    Set<K> ks = keySet;
    if (ks == null) {
      ks = new KeySet();
      keySet = ks;
    }
    return ks;
  }

  private class KeySet extends AbstractSet<K> {
    public Iterator<K> iterator() {
      return new KeyIterator();
    }
    public int size() {
      return size;
    }
    public boolean contains(Object o) {
      return containsKey(o);
    }
    public boolean remove(Object o) {
      int oldSize = size;
      HashKeyValueHashMap.this.remove(o);
      return size != oldSize;
    }
    // TODO remove this commented out func.  Given this is not identity-based it should be safe to omit this
//    /*
//     * Must revert from AbstractSet's impl to AbstractCollection's, as
//     * the former contains an optimization that results in incorrect
//     * behavior when c is a smaller "normal" (non-identity-based) Set.
//     */
//    public boolean removeAll(Collection<?> c) {
//      Objects.requireNonNull(c);
//      boolean modified = false;
//      for (Iterator<K> i = iterator(); i.hasNext(); ) {
//        if (c.contains(i.next())) {
//          i.remove();
//          modified = true;
//        }
//      }
//      return modified;
//    }
    public void clear() {
      HashKeyValueHashMap.this.clear();
    }
    public int hashCode() {
      int result = 0;
      for (K key : this)
        result += Objects.hashCode(key);
      return result;
    }
    public Object[] toArray() {
      return toArray(new Object[0]);
    }
    @SuppressWarnings("unchecked")
    public <T> T[] toArray(T[] a) {
      int expectedModCount = modCount;
      int size = size();
      if (a.length < size)
        a = (T[]) Array.newInstance(a.getClass().getComponentType(), size);
      MaskedHashKeyValue[] tab = table;
      int ti = 0;
      for (int si = 0; si < tab.length; si++ ) {
        Object key;
        if ((key = tab[si].key) != null) { // key present ?
          // more elements than expected -> concurrent modification from other thread
          if (ti >= size) {
            throw new ConcurrentModificationException();
          }
          a[ti++] = (T) unmaskNull(key); // unmask key
        }
      }
      // fewer elements than expected or concurrent modification from other thread detected
      if (ti < size || expectedModCount != modCount) {
        throw new ConcurrentModificationException();
      }
      // final null marker as per spec
      if (ti < a.length) {
        a[ti] = null;
      }
      return a;
    }

    public Spliterator<K> spliterator() {
      return new KeySpliterator<>(HashKeyValueHashMap.this, 0, -1, 0, 0);
    }
  }

  /**
   * Returns a {@link Collection} view of the values contained in this map.
   * The collection is backed by the map, so changes to the map are
   * reflected in the collection, and vice-versa.  If the map is
   * modified while an iteration over the collection is in progress,
   * the results of the iteration are undefined.  The collection
   * supports element removal, which removes the corresponding
   * mapping from the map, via the {@code Iterator.remove},
   * {@code Collection.remove}, {@code removeAll},
   * {@code retainAll} and {@code clear} methods.  It does not
   * support the {@code add} or {@code addAll} methods.
   *
   * <p><b>While the object returned by this method implements the
   * {@code Collection} interface, it does <i>not</i> obey
   * {@code Collection's} general contract.  Like its backing map,
   * the collection returned by this method defines element equality as
   * reference-equality rather than object-equality.  This affects the
   * behavior of its {@code contains}, {@code remove} and
   * {@code containsAll} methods.</b>
   */
  private Collection<V> values; // TODO remove this if this class is moved to java.util
  public Collection<V> values() {
    Collection<V> vs = values;
    if (vs == null) {
      vs = new Values();
      values = vs;
    }
    return vs;
  }

  private class Values extends AbstractCollection<V> {
    public Iterator<V> iterator() {
      return new ValueIterator();
    }
    public int size() {
      return size;
    }
    public boolean contains(Object o) {
      return containsValue(o);
    }
    public boolean remove(Object o) {
      for (Iterator<V> i = iterator(); i.hasNext(); ) {
        if (i.next() == o) {
          i.remove();
          return true;
        }
      }
      return false;
    }
    public void clear() {
      HashKeyValueHashMap.this.clear();
    }
    public Object[] toArray() {
      return toArray(new Object[0]);
    }
    @SuppressWarnings("unchecked")
    public <T> T[] toArray(T[] a) {
      int expectedModCount = modCount;
      int size = size();
      if (a.length < size)
        a = (T[]) Array.newInstance(a.getClass().getComponentType(), size);
      MaskedHashKeyValue[] tab = table;
      int ti = 0;
      for (int si = 0; si < tab.length; si++) {
        if (tab[si].key != null) { // key present ?
          // more elements than expected -> concurrent modification from other thread
          if (ti >= size) {
            throw new ConcurrentModificationException();
          }
          a[ti++] = (T) tab[si].value; // copy value
        }
      }
      // fewer elements than expected or concurrent modification from other thread detected
      if (ti < size || expectedModCount != modCount) {
        throw new ConcurrentModificationException();
      }
      // final null marker as per spec
      if (ti < a.length) {
        a[ti] = null;
      }
      return a;
    }

    public Spliterator<V> spliterator() {
      return new ValueSpliterator<>(HashKeyValueHashMap.this, 0, -1, 0, 0);
    }
  }

  /**
   * Returns a {@link Set} view of the mappings contained in this map.
   * Each element in the returned set is a reference-equality-based
   * {@code Map.Entry}.  The set is backed by the map, so changes
   * to the map are reflected in the set, and vice-versa.  If the
   * map is modified while an iteration over the set is in progress,
   * the results of the iteration are undefined.  The set supports
   * element removal, which removes the corresponding mapping from
   * the map, via the {@code Iterator.remove}, {@code Set.remove},
   * {@code removeAll}, {@code retainAll} and {@code clear}
   * methods.  It does not support the {@code add} or
   * {@code addAll} methods.
   *
   * <p>Like the backing map, the {@code Map.Entry} objects in the set
   * returned by this method define key and value equality as
   * reference-equality rather than object-equality.  This affects the
   * behavior of the {@code equals} and {@code hashCode} methods of these
   * {@code Map.Entry} objects.  A reference-equality based {@code Map.Entry
   * e} is equal to an object {@code o} if and only if {@code o} is a
   * {@code Map.Entry} and {@code e.getKey()==o.getKey() &&
   * e.getValue()==o.getValue()}.  To accommodate these equals
   * semantics, the {@code hashCode} method returns
   * // TODO rewrite this (perhaps more of this comment)
   * {@code System.identityHashCode(e.getKey()) ^
   * System.identityHashCode(e.getValue())}. (While the keys and values
   * are compared using reference equality, the {@code Map.Entry}
   * objects themselves are not.)
   *
   * <p><b>Owing to the reference-equality-based semantics of the
   * {@code Map.Entry} instances in the set returned by this method,
   * it is possible that the symmetry and transitivity requirements of
   * the {@link Object#equals(Object)} contract may be violated if any of
   * the entries in the set is compared to a normal map entry, or if
   * the set returned by this method is compared to a set of normal map
   * entries (such as would be returned by a call to this method on a normal
   * map).  However, the {@code Object.equals} contract is guaranteed to
   * hold among identity-based map entries, and among sets of such entries.
   * </b>
   *
   * @return a set view of the identity-mappings contained in this map
   */
  public Set<Map.Entry<K,V>> entrySet() {
    Set<Map.Entry<K,V>> es = entrySet;
    if (es != null)
      return es;
    else
      return entrySet = new EntrySet();
  }

  private class EntrySet extends AbstractSet<Map.Entry<K,V>> {
    public Iterator<Map.Entry<K,V>> iterator() {
      return new EntryIterator();
    }
    public boolean contains(Object o) {
      return o instanceof Entry<?, ?> entry
          && containsMapping(entry.getKey(), entry.getValue());
    }
    public boolean remove(Object o) {
      return o instanceof Entry<?, ?> entry
          && removeMapping(entry.getKey(), entry.getValue());
    }
    public int size() {
      return size;
    }
    public void clear() {
      HashKeyValueHashMap.this.clear();
    }
    /*
     * Must revert from AbstractSet's impl to AbstractCollection's, as
     * the former contains an optimization that results in incorrect
     * behavior when c is a smaller "normal" (non-identity-based) Set.
     */
// TODO remove this code if non-problematic.  It should not be needed as this isn't "identity-based"
//    public boolean removeAll(Collection<?> c) {
//      Objects.requireNonNull(c);
//      boolean modified = false;
//      for (Iterator<Map.Entry<K,V>> i = iterator(); i.hasNext(); ) {
//        if (c.contains(i.next())) {
//          i.remove();
//          modified = true;
//        }
//      }
//      return modified;
//    }

    public Object[] toArray() {
      return toArray(new Object[0]);
    }

    @SuppressWarnings("unchecked")
    public <T> T[] toArray(T[] a) {
      int expectedModCount = modCount;
      int size = size();
      if (a.length < size)
        a = (T[]) Array.newInstance(a.getClass().getComponentType(), size);
      MaskedHashKeyValue[] tab = table;
      int ti = 0;
      for (int si = 0; si < tab.length; si++) {
        Object key;
        if ((key = tab[si].key) != null) { // key present ?
          // more elements than expected -> concurrent modification from other thread
          if (ti >= size) {
            throw new ConcurrentModificationException();
          }
          a[ti++] = (T) new AbstractMap.SimpleEntry<>(unmaskNull(key), tab[si].value);
        }
      }
      // fewer elements than expected or concurrent modification from other thread detected
      if (ti < size || expectedModCount != modCount) {
        throw new ConcurrentModificationException();
      }
      // final null marker as per spec
      if (ti < a.length) {
        a[ti] = null;
      }
      return a;
    }

    public Spliterator<Entry<K,V>> spliterator() {
      return new EntrySpliterator<>(HashKeyValueHashMap.this, 0, -1, 0, 0);
    }
  }

  @java.io.Serial
  private static final long serialVersionUID = 8188218128353913216L;

  /**
   * Saves the state of the {@code HashKeyHashMap} instance to a stream
   * (i.e., serializes it).
   *
   * @serialData The <i>size</i> of the HashMap (the number of key-value
   *          mappings) ({@code int}), followed by the key (Object) and
   *          value (Object) for each key-value mapping represented by the
   *          HashKeyHashMap.  The key-value mappings are emitted in no
   *          particular order.
   */
  @java.io.Serial
  private void writeObject(ObjectOutputStream s) throws java.io.IOException {
    // Write out size (number of mappings) and any hidden stuff
    s.defaultWriteObject();

    // Write out size again (maintained for backward compatibility)
    s.writeInt(size);

    // Write out keys and values (alternating)
    MaskedHashKeyValue[] tab = table;
    for (int i = 0; i < tab.length; i++) {
      Object key = tab[i].key;
      if (key != null) {
        s.writeObject(unmaskNull(key));
        s.writeObject(tab[i].value);
      }
    }
  }

  /**
   * Reconstitutes the {@code HashKeyHashMap} instance from a stream (i.e.,
   * deserializes it).
   */
  @java.io.Serial
  private void readObject(ObjectInputStream s)
      throws java.io.IOException, ClassNotFoundException  {
    // Size (number of mappings) is written to the stream twice
    // Read first size value and ignore it
    s.readFields();

    // Read second size value, validate and assign to size field
    int size = s.readInt();
    if (size < 0)
      throw new java.io.StreamCorruptedException
          ("Illegal mappings count: " + size);
    int cap = capacity(size);
    // TODO serialization not correctly handled because can't access from outside java.util?: SharedSecrets.getJavaObjectInputStreamAccess().checkArray(s, Object[].class, cap*3);
    this.size = size;
    init(cap);

    // Read the keys and values, and put the mappings in the table
    for (int i=0; i<size; i++) {
      @SuppressWarnings("unchecked")
      K key = (K) s.readObject();
      @SuppressWarnings("unchecked")
      V value = (V) s.readObject();
      putForCreate(key, value);
    }
  }

  /**
   * The put method for readObject.  It does not resize the table,
   * update modCount, etc.
   */
  private void putForCreate(K key, V value)
      throws java.io.StreamCorruptedException
  {
    Object k = maskNull(key);
    int keyHash = k.hashCode();
    MaskedHashKeyValue[] tab = table;
    int len = tab.length;
    int i = getIndex(keyHash, len);

    MaskedHashKeyValue item;
    while ( (item = tab[i]) != null) {
      if (item.key.equals(k))
        throw new java.io.StreamCorruptedException();
      i = nextKeyIndex(i, len);
    }
    tab[i] = new MaskedHashKeyValue(keyHash, k, value);
  }

  @SuppressWarnings("unchecked")
  @Override
  public void forEach(BiConsumer<? super K, ? super V> action) {
    Objects.requireNonNull(action);
    int expectedModCount = modCount;

    MaskedHashKeyValue[] t = table;
    for (int index = 0; index < t.length; index++) {
      Object k = t[index].key; // TODO is it better to assign t[index] to a local var, E, and use E?  If so look at all places in this file where the array lookup is done.
      if (k != null) {
        action.accept((K) unmaskNull(k), (V) t[index].value);
      }

      if (modCount != expectedModCount) {
        throw new ConcurrentModificationException();
      }
    }
  }

  @SuppressWarnings("unchecked")
  @Override
  public void replaceAll(BiFunction<? super K, ? super V, ? extends V> function) {
    Objects.requireNonNull(function);
    int expectedModCount = modCount;

    MaskedHashKeyValue[] t = table;
    for (int index = 0; index < t.length; index++) {
      final MaskedHashKeyValue item = t[index];
      Object k = item.key;
      if (k != null) {
        t[index] = new MaskedHashKeyValue(item.maskedHash, k, function.apply((K) unmaskNull(k), (V) t[index].value));
      }

      if (modCount != expectedModCount) {
        throw new ConcurrentModificationException();
      }
    }
  }
  /**
   * {@inheritDoc}
   *
   * <p>More formally, if this map contains a mapping from a key
   * {@code k} to a value {@code v} such that {@code (key == k)}
   * and {@code (value == v)}, then this method removes the mapping
   * for this key and returns {@code true}; otherwise it returns
   * {@code false}.
   */
  @Override
  public boolean remove(Object key, Object value) {
    return removeMapping(key, value);
  }

  /**
   * {@inheritDoc}
   *
   * <p>More formally, if this map contains a mapping from a key
   * {@code k} to a value {@code v} such that {@code (key == k)}
   * and {@code (oldValue == v)}, then this method associates
   * {@code k} with {@code newValue} and returns {@code true};
   * otherwise it returns {@code false}.
   */
  @Override
  public boolean replace(K key, V oldValue, V newValue) {
    Object k = maskNull(key);
    int hash = k.hashCode();
    MaskedHashKeyValue[] tab = table;
    int len = tab.length;
    int i = getIndex(hash, len);

    while (true) {
      MaskedHashKeyValue item = tab[i];
      if (item.maskedHash == hash && item.key.equals(k)) {
        if (!Objects.equals(item.value, oldValue))
          return false;
        tab[i] = new MaskedHashKeyValue(hash, k, newValue);
        return true;
      }
      if (item.key == null)
        return false;
      i = nextKeyIndex(i, len);
    }
  }

  /**
   * Similar form as array-based Spliterators, but skips blank elements,
   * and guestimates size as decreasing by half per split.
   */
  static class HashKeyValueHashMapSpliterator<K,V> {
    final HashKeyValueHashMap<K,V> map;
    int index;             // current index, modified on advance/split
    int fence;             // -1 until first use; then one past last index
    int est;               // size estimate
    int expectedModCount;  // initialized when fence set

    HashKeyValueHashMapSpliterator(HashKeyValueHashMap<K,V> map, int origin,
                                   int fence, int est, int expectedModCount) {
      this.map = map;
      this.index = origin;
      this.fence = fence;
      this.est = est;
      this.expectedModCount = expectedModCount;
    }

    final int getFence() { // initialize fence and size on first use
      int hi;
      if ((hi = fence) < 0) {
        est = map.size;
        expectedModCount = map.modCount;
        hi = fence = map.table.length;
      }
      return hi;
    }

    public final long estimateSize() {
      getFence(); // force init
      return (long) est;
    }
  }

  static final class KeySpliterator<K,V>
      extends HashKeyValueHashMapSpliterator<K,V>
      implements Spliterator<K> {
    KeySpliterator(HashKeyValueHashMap<K,V> map, int origin, int fence, int est,
             int expectedModCount) {
      super(map, origin, fence, est, expectedModCount);
    }

    public KeySpliterator<K,V> trySplit() {
      int hi = getFence(), lo = index, mid = ((lo + hi) >>> 1);
      return (lo >= mid) ? null :
          new KeySpliterator<>(map, lo, index = mid, est >>>= 1,
              expectedModCount);
    }

    @SuppressWarnings("unchecked")
    public void forEachRemaining(Consumer<? super K> action) {
      if (action == null)
        throw new NullPointerException();
      int i, hi, mc; Object key;
      HashKeyValueHashMap<K,V> m; MaskedHashKeyValue[] a;
      if ((m = map) != null && (a = m.table) != null &&
          (i = index) >= 0 && (index = hi = getFence()) <= a.length) {
        for (; i < hi; i++) {
          if ((key = a[i].key) != null)
            action.accept((K)unmaskNull(key));
        }
        if (m.modCount == expectedModCount)
          return;
      }
      throw new ConcurrentModificationException();
    }

    @SuppressWarnings("unchecked")
    public boolean tryAdvance(Consumer<? super K> action) {
      if (action == null)
        throw new NullPointerException();
      MaskedHashKeyValue[] a = map.table;
      int hi = getFence();
      while (index < hi) {
        Object key = a[index].key;
        index++;
        if (key != null) {
          action.accept((K) unmaskNull(key));
          if (map.modCount != expectedModCount)
            throw new ConcurrentModificationException();
          return true;
        }
      }
      return false;
    }

    public int characteristics() {
      return (fence < 0 || est == map.size ? SIZED : 0) | Spliterator.DISTINCT;
    }
  }

  static final class ValueSpliterator<K,V>
      extends HashKeyValueHashMapSpliterator<K,V>
      implements Spliterator<V> {
    ValueSpliterator(HashKeyValueHashMap<K,V> m, int origin, int fence, int est,
        int expectedModCount) {
      super(m, origin, fence, est, expectedModCount);
    }

    public ValueSpliterator<K,V> trySplit() {
      int hi = getFence(), lo = index, mid = ((lo + hi) >>> 1);
      return (lo >= mid) ? null :
          new ValueSpliterator<>(map, lo, index = mid, est >>>= 1,
              expectedModCount);
    }

    public void forEachRemaining(Consumer<? super V> action) {
      if (action == null)
        throw new NullPointerException();
      int i, hi, mc;
      HashKeyValueHashMap<K,V> m; MaskedHashKeyValue[] a;
      if ((m = map) != null && (a = m.table) != null &&
          (i = index) >= 0 && (index = hi = getFence()) <= a.length) {
        for (; i < hi; i++) {
          if (a[i].key != null) {
            @SuppressWarnings("unchecked") V v = (V)a[i].value;
            action.accept(v);
          }
        }
        if (m.modCount == expectedModCount)
          return;
      }
      throw new ConcurrentModificationException();
    }

    public boolean tryAdvance(Consumer<? super V> action) {
      if (action == null)
        throw new NullPointerException();
      MaskedHashKeyValue[] a = map.table;
      int hi = getFence();
      while (index < hi) {
        MaskedHashKeyValue elem = a[index];
        @SuppressWarnings("unchecked") V v = (V)elem.value;
        index++;
        if (elem.key != null) {
          action.accept(v);
          if (map.modCount != expectedModCount)
            throw new ConcurrentModificationException();
          return true;
        }
      }
      return false;
    }

    public int characteristics() {
      return (fence < 0 || est == map.size ? SIZED : 0);
    }

  }

  static final class EntrySpliterator<K,V>
      extends HashKeyValueHashMapSpliterator<K,V>
      implements Spliterator<Map.Entry<K,V>> {
    EntrySpliterator(HashKeyValueHashMap<K,V> m, int origin, int fence, int est,
        int expectedModCount) {
      super(m, origin, fence, est, expectedModCount);
    }

    public EntrySpliterator<K,V> trySplit() {
      int hi = getFence(), lo = index, mid = ((lo + hi) >>> 1);
      return (lo >= mid) ? null :
          new EntrySpliterator<>(map, lo, index = mid, est >>>= 1,
              expectedModCount);
    }

    public void forEachRemaining(Consumer<? super Map.Entry<K, V>> action) {
      if (action == null)
        throw new NullPointerException();
      int i, hi, mc;
      HashKeyValueHashMap<K,V> m; MaskedHashKeyValue[] a;
      if ((m = map) != null && (a = m.table) != null &&
          (i = index) >= 0 && (index = hi = getFence()) <= a.length) {
        for (; i < hi; i++) {
          if (a[i].key != null) {
            @SuppressWarnings("unchecked") K k =
                (K)unmaskNull(a[i].key);
            @SuppressWarnings("unchecked") V v = (V)a[i].value;
            action.accept
                (new AbstractMap.SimpleImmutableEntry<>(k, v));

          }
        }
        if (m.modCount == expectedModCount)
          return;
      }
      throw new ConcurrentModificationException();
    }

    public boolean tryAdvance(Consumer<? super Map.Entry<K,V>> action) {
      if (action == null)
        throw new NullPointerException();
      MaskedHashKeyValue[] a = map.table;
      int hi = getFence();
      while (index < hi) {
        Object key = a[index].key;
        @SuppressWarnings("unchecked") V v = (V)a[index].value;
        index++;
        if (key != null) {
          @SuppressWarnings("unchecked") K k =
              (K)unmaskNull(key);
          action.accept
              (new AbstractMap.SimpleImmutableEntry<>(k, v));
          if (map.modCount != expectedModCount)
            throw new ConcurrentModificationException();
          return true;
        }
      }
      return false;
    }

    public int characteristics() {
      return (fence < 0 || est == map.size ? SIZED : 0) | Spliterator.DISTINCT;
    }
  }

  static final /*TODO primitive*/ class MaskedHashKeyValue {
    final int maskedHash;
    final Object key; // TODO make this K if possible.  To do so must deal with NULL_KEY
    final Object value; // TODO make this V if possible.

    static final MaskedHashKeyValue EMPTY = new MaskedHashKeyValue(0, null, null);

    MaskedHashKeyValue(int maskedHash, Object key, Object value) {
      this.maskedHash = maskedHash;
      this.key = key;
      this.value = value;
    }
  }
}

/* TODO  "X & ~1" returns X if it is even else X+1.  This could maybe be used to have a Hash and Index where the index is two shorts combined in one int
// Ignore signed ints (or signed shorts) for now.  Given
0: hash0
1: hash1
2: index0index1
3: hash3
4: hash4
5: index3index4
...

The location for the index is X
its index is in (X & ~1) + 2
the mask is 15 << (X&1)
*/

/*
Transfer all the hash email notes to be to do's inside one of the files. Don't forget to have the integer to integer map is an abstraction that can be used to have multiple indices on the same array, or if they're just happens to be an array that you want to reference.

Propose a one-way shift of a Java pojo that would change its class without changing the address of the pojo and reconfigure it Scott's rather like a butterfly to match the data structures. The overall footprint of the object should not change, so it should be the maximum size of its possible incarnations.

Consider having a test that puts a lot of pressure on memory. So instead of testing one hash map of different kinds test hundreds so that each lookup will not be in level three cash, whatever that means.

Do test the for Charles to too shorts to see if it has good performance. It does have very nice cash hit properties.

Test the growing hash table hypothesis to change from two shorts with char too. Integer with shorts to all. Integer

Do a test with an object that has a poorly distributed hash code and see what the effect is if we don't have the tree map things and what can be done to mitigate this.




Transfer all the hash email notes to be to do's inside one of the files. Don't forget to have the integer to integer map is an abstraction that can be used to have multiple indices on the same array, or if they're just happens to be an array that you want to reference.

Propose a one-way shift of a Java pojo that would change its class without changing the address of the pojo and reconfigure it Scott's rather like a butterfly to match the data structures. The overall footprint of the object should not change, so it should be the maximum size of its possible incarnations.

Consider having a test that puts a lot of pressure on memory. So instead of testing one hash map of different kinds test hundreds so that each lookup will not be in level three cash, whatever that means.

Do test the for Charles to too shorts to see if it has good performance. It does have very nice cash hit properties.

Test the growing hash table hypothesis to change from two shorts with char too. Integer with shorts to all. Integer

Do a test with an object that has a poorly distributed hash code and see what the effect is if we don't have the tree map things and what can be done to mitigate this.



https://cr.openjdk.org/~skuksenko/valhalla/hashmaps/hash.html

Reconsider the computation of the hash modulo equivalent. The current one does a bad job if the size is less than 2^16.  See if there's a way to use bitwise operations to take account of the current size when doing this salting.

 */
