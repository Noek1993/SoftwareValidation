/**
 * Represents the board of the game. For simplicity the board is always square.
 */
final class Board {

  /** @informal The board has a positive size, is a square, and all items are defined. */
  //@ public invariant xSize > 0 && ySize > 0;
  //@ public invariant xSize == ySize;
  //@ public invariant \forall int x,y; x >= 0 && x < xSize && y >= 0 && y < ySize; items[x][y] != null;
  /** @informal All marked locations are in the valid playing area (that is, on the ground) */
  // See BoardItem.java
  /** @informal All crates are in the valid playing area */
  // See BoardItem.java
	
  /*@ spec_public @*/ int xSize; 
  /*@ spec_public @*/ int ySize; 

  public BoardItem[][] items;

  /** @informal based on valid parameters the constructor creates an "all wall" board */
  //@ requires xSize > 0 && ySize > 0 && xSize == ySize;
  //@ ensures \forall int x,y; x >= 0 && x < xSize && y >= 0 && y < ySize; items[x][y].ground == false;
  //@ ensures items.length == xSize && items[0].length == ySize;
  Board (int xSize, int ySize) {
    this.xSize = xSize;
    this.ySize = ySize;
    items = new BoardItem[xSize][ySize];
    for (int x = 0; x < xSize; x++) {
        for (int y = 0; y < ySize; y++) {
            items[x][y] = new BoardItem();
        }
    }
  }
  
  /** @informal auxiliary method to establish that a position is on the board */
  //@ ensures \result == 0 <= p.x && p.x < xSize && 0 <= p.y && p.y < ySize;
  public /*@ pure @*/ boolean onBoard(Position p) {
      return 0 <= p.x && p.x < xSize && 0 <= p.y && p.y < ySize;
  }

  /** @informal same as above for explicit coordinates */
  //@ ensures \result == 0 <= x && x < xSize && 0 <= y && y < ySize;
  public /*@ pure @*/ boolean onBoard(int x, int y) {
      return 0 <= x && x < xSize && 0 <= y && y < ySize;
  }

  /** @informal auxiliary method to establish that a position is on board and is open
   *     (the player can stand on it) */
  //@ requires onBoard(p);
  //@ ensures \result == items[p.x][p.y].ground && !items[p.x][p.y].crate;
  //@ also
  //@ requires !onBoard(p);
  //@ ensures \result == false;
  public /*@ pure @*/ boolean isOpen(/*@ non_null @*/ Position p) {
	  if(!onBoard(p)) return false;
	  return items[p.x][p.y].ground && !items[p.x][p.y].crate; 
  }

  /** @informal same as above for explicit coordinates */
  //@ requires onBoard(x, y);
  //@ ensures \result == items[x][y].ground && !items[x][y].crate;
  //@ also
  //@ requires !onBoard(x, y);
  //@ ensures \result == false;
  public /*@ pure @*/boolean isOpen(int x, int y) {
	  if(!onBoard(x, y)) return false;
	  return items[x][y].ground && !items[x][y].crate; 
  }

  //@ skipesc
  public /*@ pure non_null @*/ String toString () {
	String r = "";
	for(int y=0; y<ySize; y++) {
	    for(int x=0; x<xSize; x++)
			r += items[x][y];
		r += "\n";
	}
    return r;
  }
  
}
