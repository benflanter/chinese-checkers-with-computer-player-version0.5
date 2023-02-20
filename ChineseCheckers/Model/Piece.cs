using System;
using System.Drawing;

namespace ChineseCheckers
{
    public class Piece
    {
		public int row, col;
        public bool side;
		public const int X_STEP = 27;
		public const int Y_STEP = 45;
		public const int PieceSize = 55;
		public bool empty;

		public Piece(int row, int col, bool side)
		{
			this.row = row;
			this.col = col;
			this.side = side;
			this.empty = false;
		}

        public Piece(int row, int col)
        {
            this.row = row;
            this.col = col;
            this.side = false;
            this.empty = true;
        }

        public void Draw(Graphics graphics)
		{
			Image img = side ? Properties.Resources.Black : Properties.Resources.Red;
			graphics.DrawImage(img, col * X_STEP + Board.STARTX - 10,  row * Y_STEP + Board.STARTY,
				                         PieceSize + 6, PieceSize);
			
		}
	}
}