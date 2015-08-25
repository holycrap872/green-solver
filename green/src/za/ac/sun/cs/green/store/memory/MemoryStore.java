package za.ac.sun.cs.green.store.memory;

import java.io.IOException;
import java.io.Serializable;
import java.util.Properties;
import java.util.logging.Level;

import za.ac.sun.cs.green.Green;
import za.ac.sun.cs.green.store.BasicStore;
import za.ac.sun.cs.green.util.Configuration;
import za.ac.sun.cs.green.util.Reporter;
import java.util.Map;
import java.util.HashMap;

/**
 * An implementation of a {@link za.ac.sun.cs.green.store.Store} based on redis (<code>http://www.redis.io</code>).
 * 
 * @author Jaco Geldenhuys <jaco@cs.sun.ac.za>
 */
public class MemoryStore extends BasicStore {

	/**
	 * Number of times <code>get(...)</code> was called.
	 */
	private int retrievalCount = 0;

	/**
	 * Number of times <code>put(...)</code> was called.
	 */
	private int insertionCount = 0;

        /**
         * Map that stores values in memory
         */
        private Map<Integer,String> map;

	/**
	 * Constructor to create a default connection to a redis store running on the local computer.
	 */
	public MemoryStore(Green solver, Properties properties) {
		super(solver);
		map = new HashMap<Integer,String>();
	}
	
	@Override
	public void report(Reporter reporter) {
		reporter.report(getClass().getSimpleName(), "retrievalCount = " + retrievalCount);
		reporter.report(getClass().getSimpleName(), "insertionCount = " + insertionCount);
	}
	
	@Override
	public synchronized Object get(String key) {
		retrievalCount++;
		try {
			String s = map.get(key.hashCode());
			return (s == null) ? null : fromString(s);
		} catch (IOException x) {
			log.log(Level.SEVERE, "io problem", x);
		} catch (ClassNotFoundException x) {
			log.log(Level.SEVERE, "class not found problem", x);
		}
		return null;
	}

	@Override
	public synchronized void put(String key, Serializable value) {
		insertionCount++;
		try {
			map.put(key.hashCode(), toString(value));
			System.out.println(key.hashCode() + "->" + toString(value));
		} catch (IOException x) {
			log.log(Level.SEVERE, "io problem", x);
		}
	}
}
