package za.ac.sun.cs.green.klee;

import static org.junit.Assert.*;

import java.util.HashSet;
import java.util.Set;

import org.junit.Test;

import za.ac.sun.cs.green.resources.HashSetMap;

public class HashSetMapTest {

	@Test
	public void test01() {
		HashSetMap<Integer> hsm = new HashSetMap<Integer>();
		Set<Integer> set = new HashSet<Integer>();
		set.add(Integer.valueOf(1));
		set.add(Integer.valueOf(2));
		set.add(Integer.valueOf(3));
		
		hsm.addAll(set);
		
		assertEquals(hsm.getValues().size(), 1);
		assertTrue(hsm.getValues().iterator().next().contains(Integer.valueOf(1)));
		assertTrue(hsm.getValues().iterator().next().contains(Integer.valueOf(2)));
		assertTrue(hsm.getValues().iterator().next().contains(Integer.valueOf(3)));
		
		assertEquals(hsm.getValue(Integer.valueOf(1)), set);
		assertEquals(hsm.getValue(Integer.valueOf(2)), set);
		assertEquals(hsm.getValue(Integer.valueOf(3)), set);
	}

	@Test
	public void test02() {
		HashSetMap<Integer> hsm = new HashSetMap<Integer>();
		Set<Integer> set = new HashSet<Integer>();
		set.add(Integer.valueOf(1));
		set.add(Integer.valueOf(2));
		set.add(Integer.valueOf(3));
		
		hsm.addAll(set);
		
		assertEquals(hsm.getValues().size(), 1);
		assertTrue(hsm.getValues().iterator().next().contains(Integer.valueOf(1)));
		assertTrue(hsm.getValues().iterator().next().contains(Integer.valueOf(2)));
		assertTrue(hsm.getValues().iterator().next().contains(Integer.valueOf(3)));
		
		assertEquals(hsm.getValue(Integer.valueOf(1)), set);
		assertEquals(hsm.getValue(Integer.valueOf(2)), set);
		assertEquals(hsm.getValue(Integer.valueOf(3)), set);
		
		Set<Integer> newSet = new HashSet<Integer>();
		newSet.add(Integer.valueOf(4));
		hsm.put(Integer.valueOf(1), newSet);
		
		assertEquals(hsm.getValues().size(), 1);
		assertEquals(hsm.getValues().iterator().next().size(), 1);
		assertTrue(hsm.getValues().iterator().next().contains(Integer.valueOf(4)));
		
		assertEquals(hsm.getValue(Integer.valueOf(1)), newSet);
		assertEquals(hsm.getValue(Integer.valueOf(2)), newSet);
		assertEquals(hsm.getValue(Integer.valueOf(3)), newSet);
	}
	
	@Test
	public void test03() {
		HashSetMap<Integer> hsm = new HashSetMap<Integer>();
		Set<Integer> set = new HashSet<Integer>();
		set.add(Integer.valueOf(1));

		assertNull(hsm.put(Integer.valueOf(1), set));
		
	}
}
