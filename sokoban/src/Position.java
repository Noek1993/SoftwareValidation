/**
 * Stores coordinates of the position on the board.
 */
final class Position
{

  /** @informal only allow positive positions */
  //@ invariant x >= 0 && y >= 0;
  /*@ spec_public @*/final int x;
  /*@ spec_public @*/final int y;

  /** @informal based on valid parameters the constructor creates a valid position object */
  //@ assignable this.x;
  //@ assignable this.y;
  //@ requires x >= 0 && y >= 0;
  //@ ensures x == this.x && y == this.y;
  Position (int x, int y) {
    this.x = x;
    this.y = y;
  }

  /** @informal to be equal positions need to agree on both coordinates */ 
  //@ assignable \nothing;
  //@ requires o instanceof Position;
  //@ ensures \result == (((Position) o).x == x && ((Position) o).y == y);
  //@ also
  //@ assignable \nothing;
  //@ requires !(o instanceof Position);
  //@ ensures \result == false;
  public /*@ pure @*/ boolean equals (Object o) {
    if (o instanceof Position) {
      Position q = (Position) o;
      return x == q.x && y == q.y;
    }
    return false;
  }

  // This one is fixed, previously the same square or squares 1 diagonal step away were also valid
  /** @informal a valid next position is always one move horizontally
   *    or vertically from the current one */
  //@ assignable \nothing;
  //@ requires Math.abs(newPosition.x - x) + Math.abs(newPosition.y - y) == 1;
  //@ ensures \result == true;
  //@ also
  //@ assignable \nothing;
  //@ requires Math.abs(newPosition.x - x) + Math.abs(newPosition.y - y) != 1;
  //@ ensures \result == false;
  /*@ spec_public @*/
  /*@ pure @*/boolean isValidNextPosition (Position newPosition) {
	  int dX = newPosition.x - x;
	  int dY = newPosition.y - y;
	  if(Math.abs(dX) + Math.abs(dY) == 1) return true;
	  return false;
  }

  //@ skipesc
  public /*@ pure non_null @*/ String toString () {
    return "position(" + this.x + "," + this.y + ")";
  }

}
