/**
 * The game of Sokoban is played on a (for simplicity) square board. Each
 * cell of the board is occupied by either:
 *   
 *   - a wall, which is impenetrable
 *   - a ground that can be marked. Marked ground squares have to be covered with
 *     crates to win the game
 *   - a box/crate that can be moved one cell in a horizontal or vertical direction,
 *     provided there is no obstruction behind the crate
 *     (the real Sokoban game also requires that the amount of crates is exactly the same 
 *     as the amount of marked squares, here we relax this requirement, that is, there might
 *     be more crates than marks)
 *   - a player itself, that is initially placed on an unoccupied spot and
 *     can move horizontally or vertically, but not diagonally, one position keeping
 *     in mind the game rules.
 * 
 * The game is won when the player rearranges the board such that all marked ground
 * squares are covered by crates.
 */
final class Game {

  Board board;
  Player player;

  /** @informal Some consistency properties:
       - a player has to be within the bounds of the board
       - a player can only stand on a board square that is not occupied (by a wall or a crate) 
       (hint - repeating some invariants stated in Board might speed up ESC on wonGame) */
  
  /** @informal based on valid parameters the constructor creates a valid game object */
  //@ assignable this.board;
  //@ assignable this.player;
  //@ ensures this.board == board;
  //@ ensures this.player == player;
  Game ( /*@ non_null @*/ Board board, /*@ non_null @*/ Player player) {
    this.board = board;
    this.player = player;
  }

  /** @informal Check precisely for the win situation */
  //@ assignable \nothing;
  //@ ensures \result == (\forall int x; x >= 0 && x < board.xSize; (\forall int y; y >= 0 && y < board.ySize; board.items[x][y].marked ==> board.items[x][y].crate));
  /*@ pure @*/ boolean wonGame () {
    boolean result = true;
    //@ loop_invariant x >= 0 && x <= board.xSize;
    //@ loop_invariant result == \forall int i; i >= 0 && i < x; (\forall int j; j >= 0 && j < board.ySize; !board.items[i][j].marked || board.items[i][j].crate);
    //@ decreases board.xSize - x;
    for (int x = 0; result && x < board.xSize; x++) {
        boolean rowresult = true;
        //@ loop_invariant y >= 0 && y <= board.ySize;
        //@ loop_invariant rowresult == (\forall int i; i >= 0 && i < y; !board.items[x][i].marked || board.items[x][i].crate);
        //@ decreases board.ySize - y;
        for (int y = 0; rowresult && y < board.ySize; y++) {
            if (board.items[x][y].marked && !board.items[x][y].crate) {
              rowresult = false; 
            }
        }
        result = rowresult;
    }
    return result;
  }

  /** @informal The core of the game - checks the validity of the move,
    *  moves the player to new position, rearranges the board.
    */
  //@ normal_behaviour
  //@ requires !player.position.isValidNextPosition (newPosition);
  //@ ensures \result == false;
  //@ also normal_behaviour
  //@ requires !board.onBoard(newPosition);
  //@ ensures \result == false;
  //@ also normal_behaviour
  //@ requires !board.items[newPosition.x][newPosition.y].ground;
  //@ ensures \result == false;
  //@ also normal_behaviour
  //@ requires board.isOpen(newPosition);
  //@ requires player.position.isValidNextPosition (newPosition);
  //@ requires board.onBoard(newPosition);
  //@ ensures \result == true;
  //@ also normal_behaviour
  //@ requires board.onBoard(newPosition);
  //@ requires board.items[newPosition.x][newPosition.y].crate;
  //@ requires player.position.isValidNextPosition (newPosition);
  //@ requires board.isOpen(newPosition.x + (newPosition.x - player.position.x), newPosition.y + (newPosition.y - player.position.y));
  //@ ensures \result == true;
  //@ also normal_behaviour
  //@ requires board.onBoard(newPosition);
  //@ requires board.items[newPosition.x][newPosition.y].crate;
  //@ requires player.position.isValidNextPosition (newPosition);
  //@ requires !board.isOpen(newPosition.x + (newPosition.x - player.position.x), newPosition.y + (newPosition.y - player.position.y));
  //@ ensures \result == false;
  boolean movePlayer (Position newPosition) {

    // First a light check if the move is allowed and the position is OK
    if (!player.position.isValidNextPosition (newPosition) || !board.onBoard(newPosition) || !board.items[newPosition.x][newPosition.y].ground) {
      return false;
    }

    /** @informal Re-check that the new position is on the board */
    //@ assert board.onBoard(newPosition);

    // If the new position is not a crate just move
    if (!board.items[newPosition.x][newPosition.y].crate) {
      player.setPosition (newPosition);
      return true;
    }

    /** @informal Last case, it has to be crate, check that */
    //@ assert board.items[newPosition.x][newPosition.y].crate;

    // make the move together with the crate if possible */
    int xShift = newPosition.x - player.position.x;
    int yShift = newPosition.y - player.position.y;

    // The new position of the moved item:
    int nX = newPosition.x + xShift;
    int nY = newPosition.y + yShift;

    // See if the new position for the crate is OK
    if (!board.isOpen(nX, nY)) {
      return false;
    }
    //@ assert board.isOpen(nX, nY);

    // Move the crate, change markings accordingly.
    board.items[newPosition.x][newPosition.y].crate = false; // old position of crate
    board.items[nX][nY].crate = true; // new position of crate

    player.setPosition (newPosition);
    return true;
  }

  //@ skipesc
  public /*@ non_null pure @*/ String toString (){
    return ""+board+player+"\n";
  }

  //@ skipesc
  public static void main (String[]args) {
    Player p = new Player (new Position (4, 4));
    Board b = new Board (9, 9);
    for (int x = 1; x < 8; x++) {
    	for (int y=1; y<8; y++) {
    		b.items[x][y].ground = true;
    	}
    }
    // Sample board arrangement
    b.items[1][1].crate = true;
    b.items[1][3].crate = true;
    b.items[1][5].crate = true;
    b.items[1][7].crate = true;
    b.items[7][1].crate = true;
    b.items[7][3].crate = true;
    b.items[7][5].crate = true;
    b.items[7][7].crate = true;
    b.items[3][1].crate = true;
    b.items[5][1].crate = true;
    b.items[3][7].crate = true;
    b.items[5][7].crate = true;
    b.items[1][3].crate = true;
    b.items[1][5].crate = true;
    b.items[2][2].crate = true;
    b.items[2][4].crate = true;
    b.items[2][6].crate = true;
    b.items[6][2].crate = true;
    b.items[6][4].crate = true;
    b.items[6][6].crate = true;
    b.items[1][2].marked = true;
    b.items[1][4].marked = true;
    b.items[1][6].marked = true;
    b.items[7][2].marked = true;
    b.items[7][4].marked = true;
    b.items[7][6].marked = true;
    Game g = new Game (b, p);
    new GameGUI (g);
  }
}
