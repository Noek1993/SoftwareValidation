/*
 * Test data strategy for Position.
 *
 * Generated by JMLUnitNG 1.4 (116/OpenJML-20131218-REV3178), 2016-10-06 14:37 +0200.
 * (do not modify this comment, it is used by JMLUnitNG clean-up routines)
 */
import org.jmlspecs.jmlunitng.iterator.ObjectArrayIterator;
import org.jmlspecs.jmlunitng.iterator.RepeatedAccessIterator;

/**
 * Test data strategy for Position. Provides
 * class-scope test values for type java.lang.Object.
 * 
 * @author JMLUnitNG 1.4 (116/OpenJML-20131218-REV3178)
 * @version 2016-10-06 14:37 +0200
 */
public /*@ nullable_by_default */ class Position_ClassStrategy_java_lang_Object 
  extends PackageStrategy_java_lang_Object {
  /**
   * @return class-scope values for type java.lang.Object.
   */
  public RepeatedAccessIterator<?> classValues() {
    return new ObjectArrayIterator<Object>
    (new Object[] 
     { /* add class-scope java.lang.Object values or generators here */ });
  }

  /**
   * The use of reflection can be controlled here for  
   * parameters of type java.lang.Object
   * in this class by changing the parameters to <code>setReflective</code>
   * and <code>setMaxRecursionDepth<code>. 
   * In addition, the data generators used can be changed by adding 
   * additional data class lines, or by removing some of the automatically 
   * generated ones. Note that lower-level strategies can override any 
   * behavior specified here by calling the same control methods in 
   * their own constructors.
   *
   * @see NonPrimitiveStrategy#addDataClass(Class<?>)
   * @see NonPrimitiveStrategy#clearDataClasses()
   * @see ObjectStrategy#setReflective(boolean)
   * @see ObjectStrategy#setMaxRecursionDepth(int)
   */
  public Position_ClassStrategy_java_lang_Object() {
    super();
    setReflective(true);
    // uncomment to control the maximum reflective instantiation
    // recursion depth, 0 by default
    // setMaxRecursionDepth(0);
  }
}
