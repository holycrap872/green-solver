package za.ac.sun.cs.green.klee;

import static org.junit.Assert.*;

import org.junit.Test;

import za.ac.sun.cs.green.parser.klee.TestFrontEnd;

public class KleeTest {

	@Test
	public void test() {
		String[] args = {"test/za/ac/sun/cs/green/klee/files/klee.properties","test/za/ac/sun/cs/green/klee/partab"};
		TestFrontEnd.main(args);
	}
}
