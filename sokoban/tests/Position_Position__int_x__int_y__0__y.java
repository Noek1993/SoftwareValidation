/*
 * Test data strategy for Position.
 *
 * Generated by JMLUnitNG 1.4 (116/OpenJML-20131218-REV3178), 2016-10-06 14:20 +0200.
 * (do not modify this comment, it is used by JMLUnitNG clean-up routines)
 */

import org.jmlspecs.jmlunitng.iterator.ObjectArrayIterator;
import org.jmlspecs.jmlunitng.iterator.RepeatedAccessIterator;

/**
 * Test data strategy for Position. Provides
 * test values for parameter "int y" 
 * of method "Position(int, int)". 
 * 
 * @author JMLUnitNG 1.4 (116/OpenJML-20131218-REV3178)
 * @version 2016-10-06 14:20 +0200
 */
public /*@ nullable_by_default */ class Position_Position__int_x__int_y__0__y
  extends Position_ClassStrategy_int {
  /**
   * @return local-scope values for parameter 
   *  "int y".
   */
  public RepeatedAccessIterator<?> localValues() {
    return new ObjectArrayIterator<Object>
    (new Object[]
     { /* add local-scope int values or generators here */ });
  }
}
