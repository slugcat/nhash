// TODO This does not cope with poorly distributed key hash values as HashMap does in virtue of
//  using Tree buckets when the buckets are large.  It may be possible to check everywhere if the
//  key (or value?) were a tree-node, in which case use the bucket instead of looking at
//  successive slots.  This is probably would not work exactly the same because the criteria for
//  creating a bucket would be an excessively large probe count (as opposed to excessively large
//  bucket).
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
import java.io.PrintStream;
import java.lang.reflect.Array;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.*;
import java.util.function.BiConsumer;
import java.util.function.BiFunction;
import java.util.function.Consumer;

// TODO document sources:
//  https://github.com/goossaert/hashmap/blob/master/backshift_hashmap.cc seems to do the trick I thought of that with robin-hood don't need to look past the 1st entry with a greater probing distance
//
//
// TODO almost none of the javadoc has been updated.  Mostly it should look like HashMap's
/**
 * This class implements the {@code Map} interface with a hash table, using
 * reference-equality in place of object-equality when comparing keys (and
 * values).  In other words, in an {@code OpenHashMap}, two keys
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
 *   Map m = Collections.synchronizedMap(new OpenHashMap(...));</pre>
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

public class OpenHashMap<K,V> extends AbstractMap<K,V>
    implements Map<K,V>, java.io.Serializable, Cloneable
{
  static final boolean NO_PRIMITIVE = true; // supporting primitive // TODO remove this and all uses when it is no longer needed to enable compiling and debugging by IntelliJ

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
  private static final int MAXIMUM_CAPACITY = 1 << 28; // TODO don't know what this should be now.  IdentityHashMap's "29" may be influenced by the 2 cells per key/value pair in IdentityHashMap.

  /**
   * The table, resized as necessary. Length MUST always be a power of two.
   */
  transient MaskedHashKeyValue/*TODO make null-restricted: ! */[] table; // non-private to simplify nested class access
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
  static final Object NULL_KEY = new NullKeyClass();

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

  // TODO consider supporting a LinkedOpenHashMap

  /**
   * Constructs a new, empty identity hash map with a default expected
   * maximum size (21).
   */
  public OpenHashMap() {
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
  public OpenHashMap(int expectedMaxSize) {
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
    assert expectedMaxSize >= 0;
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
    assert (initCapacity & -initCapacity) == initCapacity; // power of 2
    assert initCapacity >= MINIMUM_CAPACITY;
    assert initCapacity <= MAXIMUM_CAPACITY;

    table = MaskedHashKeyValue.createEmptyFilledArray(initCapacity);
  }

  /**
   * Constructs a new identity hash map containing the keys-value mappings
   * in the specified map.
   *
   * @param m the map whose mappings are to be placed into this map
   * @throws NullPointerException if the specified map is null
   */
  public OpenHashMap(Map<? extends K, ? extends V> m) {
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
  static int getIndex(int hashCode, int length) { // TODO rename to just "indexOf"
    // TODO it seems wrong when the size is 2^24 to ignore the 1st byte and when the size is 2^8
    //  to ignore the 1st and 3rd byte.  One would think the size would be included in the
    //  expression in a way to account for this.  It may make sense for the index computation to
    //  be more elaborate for open addressing.  IdentityHashMap.hash ensures tha hash is even
    //  which this should not do.
    //  Consider passing a shift such that, at least, when table size is greater than 2^16 fewer
    //  bits are shifted since they will already be effectively used by the modulo.  The shift would be the table capacity (or that -1 or something) -- Hmm, this is something like (2^32 - length) when length > 2^16.
    return (hashCode ^ (hashCode >>> 16 )) & (length - 1); // TODO test that using '&' is actually faster than the elvis-op that is used by IdentityHashMap
  }

  /**
   * Circularly traverses table of size len.
   */
  private static int nextKeyIndex(int i, int len) {
    return (i + 1) & (len - 1); // TODO this didn't work, when it didn't work the max size was causing anomalies, so that could h
    // return (i + 1 < len ? i + 1 : 0);
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
    for (int wantedKeyHops = 0; ; wantedKeyHops++, i = nextKeyIndex(i, len)) {
      int maskedHash = tab[i].maskedHash;
      if (maskedHash == hash && k.equals(tab[i].key))
        return (V) tab[i].value;
      if (tab[i].key == null)
        return null;
      final int desiredIndexForCurrentKey = getIndex(maskedHash, len);
      final int currKeyHops = getHops(i, len, desiredIndexForCurrentKey);
      if (wantedKeyHops > currKeyHops ) {
        return null;
      }
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
      if (item.maskedHash == hash && Objects.equals(item.key, k))
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
    for (int i = 0; i < tab.length; i++) {
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
    // TODO here (and probably other places as well, should quit when numHops inequality is satisfied (as in get())
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
  @SuppressWarnings("unchecked")
  public V put(K key, V value) {
    return (V) putVal(maskNull(key), value, table, true, true, false, true);
  }

  // TODO is the overhead of calling this as a separate method plus the boolean param checks large
  //  enough to justify inlining this where it is called?
Object putVal(Object maskedKey, Object value, MaskedHashKeyValue[] tab, boolean checkKeyCanBePresentAlready, boolean tableMayNeedResizing, boolean isCopying, boolean allowResize) {
  int hash = maskedKey.hashCode();
  // TODO: decided it was better to optimize for the table-doesn't-grow vs the table-grows case since having
  //  2 loops in the doesn't-grow case seems like it would be more wasteful than redoing work
  //  when table-grows since growing is relatively rare.
  int origIndex = getIndex(hash, tab.length);
    retryAfterResize:
    for (;;) {
      final int len = tab.length;
      int i = getIndex(hash, len);
      // A "Hop" is a probe after the initial index determined by the hash.
      // "inserting" includes the initial item AND an item which has been swapped out and thus
      // needs to be re-inserted
      int insertingKeyHops = 0;

      int numKeyNotValue = 0; // TODO for debugging only.  Remove

      MaskedHashKeyValue item;
      for (Object currKey; (currKey = (item = tab[i]).key) != null;
           i = nextKeyIndex(i, len)) {
        // TODO look at jmh output size of table.  It seems high.
//        try {
//          if (++numKeyNotValue < 30 && tab[i].key != null && !tab[i].key.equals(tab[i].value)) {
//            System.out.println("capacity:" + tab.length + " size:" + this.size);
//            System.out.println("key!=value  i:" + i + " key:" + tab[i].key + " value:" + tab[i].value);
//          }
//        } catch (NullPointerException e) {
//          System.out.println("capacity:" + tab.length + " size:" + this.size);
//          System.out.println("NPE i:" + i);
//          System.out.println("NPE tab[i]" + tab[i]);
//          System.out.println("NPE tab[i].key" + tab[i].key);
//          throw e;
//        }

        if (checkKeyCanBePresentAlready && item.maskedHash == hash && currKey.equals(maskedKey)) {
          Object oldValue = item.value;
          tab[i] = new MaskedHashKeyValue(hash, maskedKey, value);
          return oldValue;
        }

        final int currHash = item.maskedHash;
        int desiredIndexForCurrentKey = getIndex(currHash, len);
        int currKeyHops = getHops(i, len, desiredIndexForCurrentKey);
        if (insertingKeyHops > currKeyHops) {
          // TODO Does the "primitive" facility (or the null-restricted value facility) have a
          //  mechanism to assign some/all of its fields to variables such that making a copy of
          //  the primitive is not required?  Or will java just optimize away this intermediary
          //  assignment?
          // Swap
          tab[i] = new MaskedHashKeyValue(hash, maskedKey, value);
          hash = currHash;
          maskedKey = currKey;
          value = item.value;
          insertingKeyHops = currKeyHops;
        }
        insertingKeyHops++;

        // TODO this is for debugging only.  Remove it
        if (insertingKeyHops > 10) {
          System.out.println("insertingKeyHops:" + insertingKeyHops + " origIndex:" + origIndex);

          List<Object[]> arrayInfo = new ArrayList<>();
          arrayInfo.add(new String[]{"i", "want-i", "probes", "hash", "key", "value"});
          for (int x = origIndex - 1; x < origIndex + 20; x++) {
            final int wantedIndex = getIndex(tab[x].maskedHash, tab.length);
            int probes = 1+getHops(x, tab.length, wantedIndex);
            arrayInfo.add(new Object[]{x, wantedIndex, probes, tab[x].maskedHash, tab[x].key, tab[x].value});
          }
          printTabularData(System.out, arrayInfo);
          System.exit(42);
        }

      }

      final int s = size + 1;
      // Use optimized form of 3 * s.
      // Next capacity is 2 * current capacity.
      if (tableMayNeedResizing) {
        if (s + (s << 1) > len << 1 && resize(len << 1)) {
          tab = table;
          continue retryAfterResize;
        }
      }
      tab[i] = new MaskedHashKeyValue(hash, maskedKey, value);
      if (!isCopying) // TODO do something about the number of these boolean params
        modCount++;
      if (allowResize)
        size = s;
      return null;
    }
  }

  /**
   * Print stats of the table to the a stream.
   * @param out a stream
   */
  public void dumpSizeStats(PrintStream out){
    out.printf("%s instance: size: %d%n", this.getClass().getName(), this.size());
    long size = heapSize();
    long bytesPer = (this.size != 0) ? size / this.size() : 0;
    out.printf("    heap size: %d(bytes), avg bytes per entry: %d, table len: %d%n\n",
        size, bytesPer, (table != null) ? table.length : 0);
  }

  private void printStats(PrintStream out, String label, int[] data, int max){
    if (data.length > 1) {
      out.printf("    %s: max: %d, mean: %3.2f, stddev: %3.2f",
          label, max > -1 ? max : data.length - 1,
          computeMean(data), computeStdDev(data));
    } else if (data.length > 0) {
      out.printf("    %s: max: %d, %s%n",
          label, max > -1 ? max : data.length - 1,
          Arrays.toString(data));
    } else {
      out.printf("    %s: n/a%n", label);
    }
  }

  private double computeStdDev ( int[] hist){
    double mean = computeMean(hist);
    double sum = 0.0f;
    long count = 0L;
    for (int i = 1; i < hist.length; i++) {
      count += hist[i];
      sum += (i - mean) * (i - mean) * hist[i];
    }
    return Math.sqrt(sum / (count - 1));
  }

  private double computeMean ( int[] hist){
    long sum = 0L;
    long count = 0;
    for (int i = 1; i < hist.length; i++) {
      count += hist[i];
      sum += i * hist[i];
    }
    return (double) sum / (double) count;
  }

  // Returns a histogram array of the number of rehashs needed to find each key.
  private long heapSize () {
    long acc = objectSizeMaybe(this);
    return acc + objectSizeMaybe(table);
    // TODO when table.length == 262144 objectSizeMaybe(table) returns 4194320.
    //  (4194320 / 262144) == 16.  16 / 3 fields == 5 bytes per field instead of 4.
    //  I'm hoping that the final version of null-restricted Value objects this will be closer to 4.
    //  The Object overhead of table should be negligible for such a large table.
  }

  private long objectSizeMaybe (Object o){
    try {
      return (mObjectSize != null)
          ? (long) mObjectSize.invoke(null, o)
          : 0L;
    } catch (IllegalAccessException | InvocationTargetException e) {
      return 0L;
    }
  }

  private static boolean hasObjectSize = false;
  private static Method mObjectSize = getObjectSizeMethod();

  private static Method getObjectSizeMethod() {
    try {
      Method m = Objects.class.getDeclaredMethod("getObjectSize", Object.class);
      hasObjectSize = true;
      return m;
    } catch (NoSuchMethodException nsme) {
      return null;
    }
  }

  public void dumpAllData(PrintStream out) {
    dump(out, 0, table.length);
  }

  public void dumpStats(PrintStream out) {
    dump(out, 0, 30);
  }

  public void dump(PrintStream out, int startIndex, int len) {
    try {
      MaskedHashKeyValue[] tab = table; // TODO remove var if don't make a dump that takes a table param (eg for the traversal table)
      out.println("size: " + size + " capacity:" + tab.length);
      dumpSizeStats(out);
      startIndex = Math.max(startIndex, 0);
      int[] probesHistogram = new int[64];
      int maxProbes = 0;
      len = Math.min(len, tab.length);
      List<Object[]> arrayInfo;
      if (len > 0) {
        arrayInfo = new ArrayList<>();
        arrayInfo.add(new String[]{"i", "want-i", "probes", "hash", "key", "value"});
      } else {
        arrayInfo = null;
      }

      int maxProbeIndex = -1;
      int numNonEmptyItems = 0;
      for (int i = 0; i < tab.length; i++) {
        final int wantedIndex = getIndex(tab[i].maskedHash, tab.length);
        int probes = 0;
        if (tab[i].key != null) {
          numNonEmptyItems++;
          probes = 1+getHops(i, tab.length, wantedIndex);
          if (i % 5_000_000 == 10) {
            System.out.println("1st loop i:" +i);
          }
          if (probes > maxProbes) {
            maxProbes = probes;
            maxProbeIndex = i;
            System.out.println("new maxProbes:" + maxProbes + " index:" + maxProbeIndex);
            int[] newProbesHistogram = new int[probesHistogram.length * 2];
            System.arraycopy(probesHistogram, 0, newProbesHistogram, 0, probesHistogram.length);
            probesHistogram = newProbesHistogram;
          }
          probesHistogram[probes]++;
        }
        if (i >= startIndex && i < startIndex + len) {
          arrayInfo.add(new Object[]{i, wantedIndex, probes, tab[i].maskedHash, tab[i].key, tab[i].value});
        }
      }

      System.out.println("2st loop");
      arrayInfo.add(new Object[]{"--", "--", "--", "--", "--", "--"});
      // Look for fishy stuff around the place where the num-probes is greatest
      for (int i = Math.max(maxProbeIndex - (maxProbes+2), 0); i < Math.min(maxProbeIndex + maxProbes +2, 300); i++) {
        final int wantedIndex = getIndex(tab[i].maskedHash, tab.length);
        int probes = 1+getHops(i, tab.length, wantedIndex);
        arrayInfo.add(new Object[]{i, wantedIndex, probes, tab[i].maskedHash, tab[i].key, tab[i].value});
      }

      out.println("numNonEmptyItems:" + numNonEmptyItems);

      out.println("probesHistogram");
      List<Object[]> probesHistogramTable = new ArrayList<>(1 + maxProbes);
      probesHistogramTable.add(new String[]{"numProbes", "count"});
      System.out.println("3rd loop");
      for (int i = 0; i < maxProbes; i++) {
        probesHistogramTable.add(new Integer[]{i, probesHistogram[i]});
      }
      System.out.println("probesHistogramTable");
      printTabularData(out, probesHistogramTable);

      System.out.println("probesStats");
      printStats(out, "probesStats", probesHistogram, maxProbes);
      out.println();
      if (arrayInfo != null) {
        printTabularData(out, arrayInfo);
      }
    } catch (Exception e) {
      e.printStackTrace(System.out);
    }
  }

  public static void printTabularData(PrintStream out, List<Object[]> data) {
    final int numCols = data.get(0).length;
    int[] maxLengths = new int[numCols];
    for (int col = 0; col < numCols; col++) {
      for (int row = 0; row < data.size(); row++) {
        String str = Objects.toString(data.get(row)[col]);
        maxLengths[col] = Math.max(maxLengths[col], str.length());
      }
    }
    for (int row = 0; row < data.size(); row++) {
      for (int col = 0; col < numCols; col++) {
        out.printf("%" + maxLengths[col] + "s ", data.get(row)[col]);
      }
      out.println();
    }
  }

  static int getHops(int i, int len, int desiredIndexForCurrentKey) {
    return (i + len - desiredIndexForCurrentKey) & (len - 1);
  }

  /**
   * Resizes the table if necessary to hold given capacity.
   *
   * @param newCapacity the new capacity, must be a power of two.
   * @return whether a resize did in fact take place
   */
  private boolean resize(int newCapacity) {
    // TODO comment out assertions
    assert (newCapacity & -newCapacity) == newCapacity : "Should be power of 2";

    // TODO just for debugging, remove
    System.out.println("Resizing  size:" + this.size + " len:" + this.table.length);

    MaskedHashKeyValue[] oldTable = table;
    int oldLength = oldTable.length;
    if (oldLength == MAXIMUM_CAPACITY) { // can't expand any further
      if (size == MAXIMUM_CAPACITY - 1)
        throw new IllegalStateException("Capacity exhausted.");
      return false;
    }
    if (oldLength >= newCapacity)
      return false;

    MaskedHashKeyValue[] newTable = MaskedHashKeyValue.createEmptyFilledArray(newCapacity);

    for (int j = 0; j < oldLength; j++) {
      MaskedHashKeyValue oldElem = oldTable[j]; // TODO be consistent using either "elem" or "item", drop one of them.
      if (oldElem.key != null) {
        putVal(oldElem.key, oldElem.value, newTable, false, false, true, false); // TODO oldElem has hash so don't re-compute it here
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

    // TODO optimize setting of hashKey if m is a OpenHashMap?
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
   * guaranteed to hold among {@code OpenHashMap} instances.</b>
   *
   * @param  o object to be compared for equality with this map
   * @return {@code true} if the specified object is equal to this map
   * @see Object#equals(Object)
   */
  public boolean equals(Object o) {
    if (o == this) {
      return true;
    } else if (o instanceof OpenHashMap<?, ?> m) {
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
   * {@code OpenHashMap} instances {@code m1} and {@code m2}, as
   * required by the general contract of {@link Object#hashCode}.
   *
   * <p><b>Owing to the reference-equality-based semantics of the
   * {@code Map.Entry} instances in the set returned by this map's
   * {@code entrySet} method, it is possible that the contractual
   * requirement of {@code Object.hashCode} mentioned in the previous
   * paragraph will be violated if one of the two objects being compared is
   * an {@code OpenHashMap} instance and the other is a normal map.</b>
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
      OpenHashMap<?,?> m = (OpenHashMap<?,?>) super.clone();
      m.entrySet = null;
      m.table = table.clone();
      return m;
    } catch (CloneNotSupportedException e) {
      throw new InternalError(e);
    }
  }

  private abstract class OpenHashMapIterator<T> implements Iterator<T> {
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
      // TODO it may not be safe to skip gap-closure for robin hood.  It at least merits trying to keep it to see if it makes the tests work.
      if (tab != OpenHashMap.this.table) {
        OpenHashMap.this.remove(key);
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
              traversalTable == OpenHashMap.this.table) {
            int remaining = len - deletedSlot;
            MaskedHashKeyValue[] newTable = MaskedHashKeyValue.createEmptyFilledArray(remaining);
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

  private class KeyIterator extends OpenHashMapIterator<K> {
    @SuppressWarnings("unchecked")
    public K next() {
      return (K) unmaskNull(traversalTable[nextIndex()].key);
    }
  }

  private class ValueIterator extends OpenHashMapIterator<V> {
    @SuppressWarnings("unchecked")
    public V next() {
      return (V) traversalTable[nextIndex()].value;
    }
  }

  private class EntryIterator
      extends OpenHashMapIterator<Entry<K,V>>
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
        if (traversalTable != OpenHashMap.this.table)
          put((K) traversalTable[index].key, value);
        return oldValue;
      }

      public boolean equals(Object o) {
        if (o == this)
          return true;

        return o instanceof Map.Entry<?, ?> e
            && Objects.equals(e.getKey(), unmaskNull(traversalTable[index].key))
            && Objects.equals(e.getValue(), traversalTable[index].value);
      }

      public int hashCode() {
        final MaskedHashKeyValue item = traversalTable[index];
        return itemUnmaskedKeyHash(item) ^ Objects.hashCode(item.value);
      }

      public String toString() {
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
      OpenHashMap.this.remove(o);
      return size != oldSize;
    }
    // TODO remove this commented out func.  Given this is not identity-based it should be safe to omit this and use inherited
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
      OpenHashMap.this.clear();
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
      return new KeySpliterator<>(OpenHashMap.this, 0, -1, 0, 0);
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
      OpenHashMap.this.clear();
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
      return new ValueSpliterator<>(OpenHashMap.this, 0, -1, 0, 0);
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
      OpenHashMap.this.clear();
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
      return new EntrySpliterator<>(OpenHashMap.this, 0, -1, 0, 0);
    }
  }

  @java.io.Serial
  private static final long serialVersionUID = 8188218128353913216L;

  /**
   * Saves the state of the {@code OpenHashMap} instance to a stream
   * (i.e., serializes it).
   *
   * @serialData The <i>size</i> of the HashMap (the number of key-value
   *          mappings) ({@code int}), followed by the key (Object) and
   *          value (Object) for each key-value mapping represented by the
   *          OpenHashMap.  The key-value mappings are emitted in no
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
   * Reconstitutes the {@code OpenHashMap} instance from a stream (i.e.,
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
    if (putVal(maskNull(key), value, table, true, false, true, true) == null
        && containsKey(unmaskNull(key))) {
      throw new java.io.StreamCorruptedException();
    }
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
  static class OpenHashMapSpliterator<K,V> {
    final OpenHashMap<K,V> map;
    int index;             // current index, modified on advance/split
    int fence;             // -1 until first use; then one past last index
    int est;               // size estimate
    int expectedModCount;  // initialized when fence set

    OpenHashMapSpliterator(OpenHashMap<K,V> map, int origin,
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
      extends OpenHashMapSpliterator<K,V>
      implements Spliterator<K> {
    KeySpliterator(OpenHashMap<K,V> map, int origin, int fence, int est,
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
      OpenHashMap<K,V> m; MaskedHashKeyValue[] a;
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
      extends OpenHashMapSpliterator<K,V>
      implements Spliterator<V> {
    ValueSpliterator(OpenHashMap<K,V> m, int origin, int fence, int est,
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
      OpenHashMap<K,V> m; MaskedHashKeyValue[] a;
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
      extends OpenHashMapSpliterator<K,V>
      implements Spliterator<Map.Entry<K,V>> {
    EntrySpliterator(OpenHashMap<K,V> m, int origin, int fence, int est,
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
      OpenHashMap<K,V> m; MaskedHashKeyValue[] a;
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

  static final /* TODO uncomment primitive*/ class MaskedHashKeyValue { // TODO restrict type by adding <K,V>
    final int maskedHash;
    final Object key;
    // TODO rename to maskedKey, and parameters.
    final Object value;

    static final MaskedHashKeyValue EMPTY = new MaskedHashKeyValue(0, null, null) /* TODO uncomment MaskedHashKeyValue.default*/;

    MaskedHashKeyValue(int maskedHash, Object key, Object value) {
      this.maskedHash = maskedHash;
      this.key = key;
      this.value = value;
    }

    static MaskedHashKeyValue[] createEmptyFilledArray(int len) {
      final MaskedHashKeyValue[] array = new MaskedHashKeyValue[len];
      if (NO_PRIMITIVE) {
        Arrays.fill(array, EMPTY);
      }
      return array;
    }

    @Override
    public String toString() {
      return "MaskedHashKeyValue{" +
          "maskedHash=" + maskedHash +
          ", key=" + key +
          ", value=" + value +
          '}';
    }
  }

  /**
   * Allows the NULL_KEY to be a unique Object that won't match any other object, and also have a
   * stable hashCode for all runs.  At minimum this facilitates gathering repeatable statistics about the distribution of hashCodes in the table.
   * TODO however if this is at all slower than the default Object.hashCode, it should be abandoned.
   */
  private static class NullKeyClass {
    @Override
    public int hashCode() {
      // "+2" because MIN_VALUE is apt to be used, and MIN_VALUE+1 could be a sentinel that isn't MIN_VALUE
      return Integer.MIN_VALUE + 2;
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

// TODO unlike HashMap this does not currently throw a ConcurrentModificationException for the compute* or merge functions.  I don't know why IdentityHashMap (from whence this implementation was derived) does not do this, so it needs to be investigated whether implementing CME in this class is feasible.

// TODO BasicSerialization test is failing.

// TODO Develop lazy add methods that wrap maps and sets
//  Just append to a list|rope until any fetch is done.  More optimal to have a lazy mode and a
//  non lazy mode in lazy mode it is legal to call put laserly and the modes are enforced by
//  having the pointer to the data structure for example the pointer to the hash table array or
//  the pointer to the rope you know and then catch it such that if cricket is never called in
//  lazy mode there will be no cost for if checks

// TODO The performance test should run multiple threads each with distinct keys and
//  values.  I think the keys should be Strings since that is more common; it
//  will also help to consume cache.  When lookup is done it should use
//  distinct keys (with the same content) to show the benefit (at least vs
//  future potential implementations of comparing with key's hashcode 1st, as
//  does the proposed implementation.  aOnly run one Map implementation at a
//  time, in multiple threads.  In this way the impact of the cache efficiency
//  of an implementation for other threads is accounted for.  That is a more
//  cache-efficient implementation will allow other threads more cache for
//  their memory needs.

// TODO I'm concerned that using Integers may allow the jvm to optimize the equals comparison such that it won't indirect off the Integer object (though I don't see how it could do this).

// TODO change indent to be 4 spaces

/* TODO document computer specs:
L1 Cache: 512KB
L2 Cache: 4MB
L3 Cache: 16MB
# of CPU Cores: 8
# of Threads: 16
AMD Ryzen™ 9 6900HX
AMD Ryzen™ 9 Mobile Processors with Radeon™ Graphics
Base Clock: 3.3GHz
Max. Boost Clock Up to 4.9GHz
16MB

The original large number is 1/2 capacity, and is large enough to make cache misses happen almost
 all the time.  There


So testing goal is to have Maps at least large enough such that (almost) every 'get' will non-cache
memory.  Since each fetch will hit a random cache line, and a cache line is 64 bytes the so there
 are 1048576 / 4 == 262144 a fetch of a 16MB array will almost always (1 out of be a miss.

16 * 1048576
167772166
16777216  / (4 bytes per field * 3 fields)
numElementsToFillCache 1398101.33333 Having this many items will fill cache.
So this * 100 means there will be a cache hit 1/100th of the time.
Since the table doubles each time it grows, and it grows when it hits 2/3 capacity then after
growth it is at 1/3 capacity.  So on average it is at 1/2 capacity.  So make the number of
elements in 'get' benchmarks be at 1/2 capacity to demonstrate average behavior for non-presized
Maps.

So 1.5 * the least power of 2 that can roughly hold numElementsToFillCache will give average
performance

1.5 * 134217728 ==

201,326,592
201326592  // This was too big so trying 1/2 of this:


A similar result would be achieved by dividing this the number of threads where each thread had a
 distinct map with distinct keys.  Ideally the number of threads would be such that the none of
 the threads get context switched.

*/
