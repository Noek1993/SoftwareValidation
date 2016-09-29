/**
 * Stores coordinates of the position on the board.
 */
final class Position
{

  /** @informal only allow positive positions */
  //@ invariant x >= 0 && y >= 0;
  /*@ spec_public */final int x;
  /*@ spec_public */final int y;

  /** @informal based on valid parameters the constructor creates a valid position object */
  //@ requires x >= 0 && y >= 0;
  //@ ensures x == this.x && y == this.y;
  Position (int x, int y) {
    this.x = x;
    this.y = y;
  }

  /** @informal to be equal positions need to agree on both coordinates */ 
  //@ requires o instanceof Position;
  //@ ensures \result == (((Position) o).x == x && ((Position) o).y == y);
  //@ also
  //@ requires !(o instanceof Position);
  //@ ensures \result == false;
  public boolean equals (Object o) {
    if (o instanceof Position) {
      Position q = (Position) o;
      return x == q.x && y == q.y;
    }
    return false;
  }

  /** @informal a valid next position is always one move horizontally
   *    or vertically from the current one */
  //@ requires Math.abs(newPosition.x - x) + Math.abs(newPosition.y - y) == 1;
  //@ ensures \result == true;
  //@ also
  //@ requires Math.abs(newPosition.x - x) + Math.abs(newPosition.y - y) != 1;
  //@ ensures \result == false;
  boolean isValidNextPosition (Position newPosition) {
	  int dX = newPosition.x - x;
	  int dY = newPosition.y - y;
	  if( dX >= -1 && dX <= 1 && dY >= -1 && dY <= 1) return true;
	  return false;
  }

  //@ skipesc
  public /*@ pure non_null @*/ String toString () {
    return "position(" + this.x + "," + this.y + ")";
  }

}
