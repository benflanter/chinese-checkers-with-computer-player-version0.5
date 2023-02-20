using System;
using System.Collections;
using System.Collections.Generic;
using System.ComponentModel;
using System.Drawing;
using System.IO;
using System.Linq;
using System.Reflection;
using System.Runtime.InteropServices.WindowsRuntime;
using System.Security.Cryptography;
using System.Text;
using System.Threading;
using System.Threading.Tasks;
using static System.Windows.Forms.VisualStyles.VisualStyleElement.ProgressBar;


namespace ChineseCheckers.Model
{
    public class ComputerPlayer : Player
    {
        private enum State { START = 1, MIDDLE, END };
        public Graph graph;
        private Dictionary<int, Piece> Base; // A dictinary of locations in the origin base that are occupied by friendly pieces
        private int prioritiyPoint = 5;
        private int destPoint = 40;
        private int destinationThreshold = 4;
        private int minDestCol = 8, maxDestCol = 15;
        private int compressionPoint = 300;
        private int avoidPoint = -1000;
        private int rearMostKey;
        private int[,] weights =
        {
            { 0,0,0,0,0,0,0,0,0,0,0,0,100,0,0,0,0,0,0,0,0,0,0,0,0 },
            { 0,0,0,0,0,0,0,0,0,0,0,100,0,100,0,0,0,0,0,0,0,0,0,0,0 },
            { 0,0,0,0,0,0,0,0,0,0,100,0,100,0,100,0,0,0,0,0,0,0,0,0,0 },
            { 0,0,0,0,0,0,0,0,0,100,0,100,0,100,0,100,0,0,0,0,0,0,0,0,0 },
            { -100,0,-60,0,-50,0,75,0,85,0,90,0,90,0,90,0,85,0,75,0,-50,0,-60,0,-100 },
            { 0,-50,0,-30,0,55,0,75,0,80,0,80,0,80,0,80,0,75,0,55,0,-30,0,-50,0 },
            { 0,0,-25,0,-20,0,55,0,65,0,70,0,70,0,70,0,65,0,55,0,-20,0,-25,0,0 },
            { 0,0,0,-15,0,-10,0,50,0,55,0,60,0,60,0,55,0,50,0,-10,0,-15,0,0,0 },
            { 0,0,0,0,-5,0,15,0,40,0,50,0,50,0,40,0,40,0,15,0,-5,0,0,0,0 },
            { 0,0,0,-5,0,10,0,30,0,40,0,40,0,40,0,40,0,30,0,10,0,-5,0,0,0 },
            { 0,0,-10,0,1,0,8,0,25,0,30,0,30,0,30,0,25,0,8,0,1,0,-10,0,0 },
            { 0,1,0,3,0,3,0,15,0,20,0,20,0,20,0,20,0,15,0,3,0,3,0,1,0 },
            { 1,0,1,0,1,0,5,0,10,0,10,0,10,0,10,0,10,0,5,0,1,0,1,0,1 },
            { 0,0,0,0,0,0,0,0,0,5,0,5,0,5,0,5,0,0,0,0,0,0,0,0,0 },
            { 0,0,0,0,0,0,0,0,0,0,3,0,3,0,3,0,0,0,0,0,0,0,0,0,0 },
            { 0,0,0,0,0,0,0,0,0,0,0,2,0,2,0,0,0,0,0,0,0,0,0,0,0 },
            { 0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0 },
        };

        public ComputerPlayer(bool side, Board board) : base(side, board)
        {
            this.rearMostKey = (Board.HEIGHT - 1) * Board.WIDTH + ((Board.WIDTH - 1) / 2);
            this.Base = new Dictionary<int, Piece>{
             { 16 * Board.WIDTH + 12, null}, { 15 * Board.WIDTH + 11,null},{ 15 * Board.WIDTH + 13,null}
            ,{ 14 * Board.WIDTH + 10,null }, { 14 * Board.WIDTH + 12,null }, { 14 * Board.WIDTH + 14,null}
            ,{ 13 * Board.WIDTH + 9,null }, { 13 * Board.WIDTH + 11,null }, { 13 * Board.WIDTH + 13,null }
            ,{ 13 * Board.WIDTH + 15,null }
            };
        }
        private Move ChooseMove()
        {
            List<Move> moves = GetMoves();
            int index = Heuristic(moves);
            Piece piece = moves[index].GetOrigin();
            int key1 = piece.row * Board.WIDTH + piece.col;
            if (Base.ContainsKey(key1))
            {
                Base.Remove(key1);
                int moveRow = moves[index].GetRow(), moveCol = moves[index].GetCol();
                int key2 = moveRow * Board.WIDTH + moveCol;
                if (Board.initmat[moveRow,moveCol] == 3)
                    Base.Add(key2, null);
            }
            return moves[index];
        }

        private State GiveStateOfGame()
        {
            State state = State.START;
            int countEnd = 0, countMid = 0;
            int lowestRow = 0;
            if (Base.Count == 0) // if origin base is not empty
            {
                foreach (Piece piece in pieces.Values)
                {
                    if (piece.row > lowestRow)
                        rearMostKey = piece.row * Board.WIDTH + piece.col;
                    if (piece.row > Board.HEIGHT / 2)
                        countMid++;
                    else if (piece.row < Board.HEIGHT / 2)
                        countEnd++;
                }
                if (countMid > pieces.Count / 2)
                    return State.MIDDLE;
                if (countEnd > pieces.Count / 2)
                    return State.END;
            }

            return state;
        }

        private bool IsDestination(int row, int col)
        {
            return (Board.initmat[row, col] == 2) && (board.getPiece(row, col) == null);
        }

        private Dictionary<int, Piece> GetDestinations()
        {
            Dictionary<int, Piece> destinations = new Dictionary<int, Piece>();
            for(int i = 0; i< this.destinationThreshold; i++)
            {
                for(int j = this.minDestCol; j <= this.maxDestCol; j++)
                {
                    if (board.getPiece(i, j) == null && Board.initmat[i,j] == 2)
                        destinations.Add(i * Board.WIDTH + j, new Piece(i,j));
                }
            }
            return destinations;
        }
        private int GetSMoves(List<Move> moves)
        {
            int index = -1;
            foreach (var move in moves)
            {
                index++;
                Piece piece = move.GetOrigin();
                if (piece.row - 4 == move.GetRow() && piece.col == move.GetCol())
                    return index;
            }
            return -1;
        } // returns the index of an S shaped move

        private int LongestJump(List<Move> moves)
        {
            double longest = 0;
            int currentIndex = -1;
            int index = -1;
            foreach (var move in moves)
            {
                currentIndex++;
                Piece piece = move.GetOrigin();
                int x = (int)Math.Pow(Math.Abs(piece.row - move.GetRow()), 2);
                int y = (int)Math.Pow(Math.Abs(piece.col - move.GetCol()), 2);
                double length = Math.Sqrt(x + y);
                if (longest == 0)
                {
                    longest = length;
                    index = currentIndex;
                }
                else if (piece.row > move.GetRow())
                {
                    if (length > longest)
                    {
                        longest = length;
                        index = currentIndex;
                    }
                }
            }
            return index;
        } // returns the index of the move with the longest distance bitween the origin piece location and the destiantion location

        private bool PieceEscaped(Move move)
        {
            Piece piece = move.GetOrigin();
            int key = move.GetRow() * Board.WIDTH + move.GetCol();
            return Base.ContainsKey(key) && !Base.ContainsKey(move.GetRow() * Board.WIDTH + move.GetCol());
        }

        private int GetMoveWeightStart(Move move)
        {
            int moveRow = move.GetRow(), moveCol = move.GetCol();
            int weight = weights[moveRow, moveCol];
            Piece piece = move.GetOrigin();
            if (PieceEscaped(move)) // check if a move will result in the removal of a piece from the origin base 
                weight += (piece.row - moveRow) * 2 * prioritiyPoint;
            if (piece.row - 4 == moveRow && piece.col == moveCol) // check Smove
                weight += prioritiyPoint;
            if (piece.row * Board.WIDTH + piece.col == rearMostKey && moveRow < piece.row) // check rearmost
                weight += prioritiyPoint;
            return weight;
        } // returns a weight for a move during the start of the game
        private int GetMoveWeightMiddle(Move move)
        {
            int moveRow = move.GetRow(), moveCol = move.GetCol();
            int weight = weights[moveRow, moveCol];
            Piece piece = move.GetOrigin();
            if (piece.row > Board.HEIGHT / 2)
                weight += (piece.row - moveRow) * 6 * prioritiyPoint;
            if (piece.row - 4 == moveRow && piece.col == moveCol) // if SMove
                weight += 3 * prioritiyPoint;
            if (piece.row < Board.HEIGHT / 4 && moveRow > piece.row) // prevent loops near dest base
                weight -= (moveRow - piece.row) * 2 * prioritiyPoint;
            int x = (int)Math.Pow(Math.Abs(piece.row - moveRow), 2);
            int y = (int)Math.Pow(Math.Abs(piece.col - moveCol), 2);
            int length = (int)Math.Sqrt(x + y);
            if (!IsDestination(moveRow,moveCol))
            {
                int deviation = 0;
                foreach (KeyValuePair<int, Piece> p in pieces)
                {
                    int row = p.Value.row, col = p.Value.col;
                    int xDev = (int)Math.Pow(Math.Abs(row - piece.row), 2);
                    int yDev = (int)Math.Pow(Math.Abs(col - piece.col), 2);
                    int dev = (int)Math.Sqrt(xDev + yDev);
                    deviation += dev;
                }
                weight += (length - deviation / 10) * prioritiyPoint;
            }
            else // if a piece is going to the dest base
                weight += destPoint * (4 - moveRow);

            return weight;
        }//  returns a weight for a move during the middle of the game
        private int GetMoveWeightEnd(Move move)
        {
            int moveRow = move.GetRow(), moveCol = move.GetCol();
            int weight = weights[moveRow, moveCol];
            Piece piece = move.GetOrigin();
            if (piece.row * Board.WIDTH + piece.col == rearMostKey && moveRow < piece.row && weight > 0) // if rearmost
                weight += (piece.row - moveRow) * destPoint * 2;
            if (Board.initmat[piece.row, piece.col] == 2) // check if you can compress the pieces in the dest base
            {
                if (moveRow < piece.row)
                    weight += (piece.row - moveRow) * compressionPoint;
                else if (moveRow > piece.row || Board.initmat[moveRow, moveCol] != 2)
                    weight += avoidPoint;
            }
            else if (IsDestination(moveRow, moveCol)) // check if you can move a piece to dest
                weight += (destinationThreshold - moveRow) * 4 * destPoint;
            else
            {
                if (CheckNextMove(move))
                    weight += 2 * destPoint;
            }
            return weight;
        } //  returns a weight for a move during the middle of the game


        private bool CheckNextMove(Move move)
        {
            bool flag = false;
            Piece originPiece = move.GetOrigin();
            int moveRow = move.GetRow(), moveCol = move.GetCol();
            Piece temp = new Piece(moveRow, moveCol,originPiece.side);
            int originKey = originPiece.row * Board.WIDTH + originPiece.col;
            int tempKey = moveRow * Board.WIDTH + moveCol;
            pieces.Remove(originKey);
            pieces.Add(tempKey, temp);
            Dictionary<int, Piece> destinations = GetDestinations();
            foreach(KeyValuePair<int, Piece> dest in destinations)
            {
                int row = dest.Value.row, col = dest.Value.col;
                if (board.MoveAble(temp, row, col))
                    flag = true;
            }
            pieces.Add(originKey, originPiece);
            pieces.Remove(tempKey);
            return flag;

        }

        private int Heuristic(List<Move> moves)
        {
            int index = -1;
            State state = GiveStateOfGame();
            if (state == State.START)
            {
                index = StartStardegy(moves);
                index = (index != -1) ? index : GetSMoves(moves);
                index = (index != -1) ? index : LongestJump(moves);
            }
            else if (state == State.MIDDLE)
            {
                index = MidStradegy(moves);
                index = (index != -1) ? index : LongestJump(moves);
            }
            else if (state == State.END)
            {
                index = EndStradegy(moves);
            }
            return index;
        }

        private int StartStardegy(List<Move> moves)
        {
            int index = -1, bestWeight = 0;
            foreach (var move in moves)
            {
                Piece piece = move.GetOrigin();
                if ((getPiece(13, 9) != null || getPiece(13, 15) != null) && move.GetRow() < piece.row)
                {
                    if ((piece.row == 13 && piece.col == 9) || (piece.row == 13 && piece.col == 15))
                    {
                        return moves.IndexOf(move);
                    }
                } // check if you can move forward the pieces in locations: (13,9) or (13,15)
                else if (Base.ContainsKey(piece.row * Board.WIDTH + piece.col))
                {
                    int weight = GetMoveWeightStart(move);
                    if (weight > bestWeight)
                    {
                        bestWeight = weight;
                        index = moves.IndexOf(move);
                    }
                } // if a move's piece is in the origin base,
                  // calculate it's weight and save the index of the move with the greatest weight
            }
            return index;
        }

        private int MidStradegy(List<Move> moves)
        {
            int index = -1;
            int bestWeight = 0;
            foreach (var move in moves)
            {
                Piece piece = move.GetOrigin();
                if (Board.initmat[piece.row, piece.col] != 2)
                {
                    int weight = GetMoveWeightMiddle(move);
                    if (weight > bestWeight)
                    {
                        bestWeight = weight;
                        index = moves.IndexOf(move);
                    } // calculate it's weight and save the index of the move with the greatest weight
                }
            }
            return index;
        }

        private int EndStradegy(List<Move> moves)
        {
            int index = -1;
            int bestWeight = 0;
            foreach (var move in moves)
            {
                Piece piece = move.GetOrigin();
                int moveRow = move.GetRow(), moveCol = move.GetCol();
                int key = moveRow * Board.WIDTH + moveCol;
                int weight = GetMoveWeightEnd(move);
                if (weight > bestWeight)
                {
                    bestWeight = weight;
                    index = moves.IndexOf(move);
                } // calculate it's weight and save the index of the move with the greatest weight
            }
            return index;
        }

        public void MakeMove()
        {
            Move move = ChooseMove();
            if (move != null)
            {
                addPiece(move.GetRow(), move.GetCol(), this.side);
                removePiece(move.GetOrigin());
            }
        }
    }
}
