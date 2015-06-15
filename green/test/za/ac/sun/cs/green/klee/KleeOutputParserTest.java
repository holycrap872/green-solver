package za.ac.sun.cs.green.klee;

import static org.junit.Assert.*;

import java.io.File;

import org.junit.Test;

import za.ac.sun.cs.green.expr.Expression;
import za.ac.sun.cs.green.parser.klee.KleeOutputParser;
import za.ac.sun.cs.green.resources.Pair;

public class KleeOutputParserTest {

	@Test
	public void test01() {
		KleeOutputParser kp = new KleeOutputParser(new File("test/za/ac/sun/cs/green/klee/files/partaa"));
	}
	
	@Test
	public void test02() {
		KleeOutputParser kp = new KleeOutputParser(new File("test/za/ac/sun/cs/green/klee/files/partaa"));
		for(int i = 0; i < 100; i ++){
			assertTrue(kp.hasNext());
		}
	}

	@Test
	public void test03() {
		KleeOutputParser kp = new KleeOutputParser(new File("test/za/ac/sun/cs/green/klee/files/partaa"));
		assertTrue(kp.hasNext());
		Pair<Expression, Boolean> t = kp.getNext();
		
		assertNotNull(t);
		assertNotNull(t.first);
		assertTrue(t.second);
		
		assertTrue(kp.hasNext());
	}
	
	@Test
	public void test04() {
		KleeOutputParser kp = new KleeOutputParser(new File("test/za/ac/sun/cs/green/klee/files/partaa"));
		assertTrue(kp.hasNext());
		Pair<Expression, Boolean> t1 = kp.getNext();
		
		assertNotNull(t1);
		assertNotNull(t1.first);
		assertTrue(t1.second);
		
		assertTrue(kp.hasNext());
		
		Pair<Expression, Boolean> t2 = kp.getNext();
		
		assertNotNull(t2);
		assertNotNull(t2.first);
		assertTrue(t2.second);
	}
	
	@Test
	public void test05() {
		KleeOutputParser kp = new KleeOutputParser(new File("test/za/ac/sun/cs/green/klee/files/partaa"));
		assertTrue(kp.hasNext());
		Pair<Expression, Boolean> t1 = kp.getNext();		
		assertNotNull(t1);
		assertNotNull(t1.first);
		assertTrue(t1.second);
		
		assertTrue(kp.hasNext());
		
		Pair<Expression, Boolean> t2 = kp.getNext();		
		assertNotNull(t2);
		assertNotNull(t2.first);
		assertTrue(t2.second);
		
		//Didn't call kp.hasNext() so should get a null value
		assertNull(kp.getNext());
	}
	
	@Test
	public void test06() {
		KleeOutputParser kp = new KleeOutputParser(new File("test/za/ac/sun/cs/green/klee/files/partaa"));
		
		//Even though there are 278 queries, 1 gets cut off
		for(int i = 0; i < 277; i ++){
			assertTrue(kp.hasNext());
			Pair<Expression, Boolean> t1 = kp.getNext();
			assertNotNull(t1);
			assertNotNull(t1.first);
			assertNotNull(t1.second);
		}
		
		assertFalse(kp.hasNext());
	}
}
