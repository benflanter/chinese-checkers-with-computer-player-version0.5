using System;
using System.Collections.Generic;
using System.Drawing.Printing;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace ChineseCheckers.Model
{
    public class Graph
    {
        private Board board;
        public Dictionary<int, List<int>> graph;
        private Dictionary<int, Tuple<int, int>> empty;
        
        public Graph(Board board)
        {
            this.board = board;
            this.graph = new Dictionary<int, List<int>>();
    
        }

        public void CreateGraph()
        {
            // Create a node for each piece on the board
            empty = new Dictionary<int, Tuple<int, int>>();
            for (int i = 0; i < Board.HEIGHT; i++)
            {
                for (int j = 0; j < Board.WIDTH; j++)
                {
                    if (Board.initmat[i, j] != 0)
                    {
                        int key = i * Board.WIDTH + j;
                        if (board.GetPieceFromKey(key) == null)
                            empty.Add(key, new Tuple<int, int>(i, j));
                            
                        graph.Add(key, new List<int>());
                    }
                }
            }

            // For each piece, find the possible destinations and create edges to them
            foreach (int key in graph.Keys)
            {
                Piece piece = board.GetPieceFromKey(key);
                List<Move> moves;
                if (piece == null)
                {
                    piece = new Piece(empty[key].Item1, empty[key].Item2);
                    moves = board.player1.GetNearMoves(piece);
                }
                else
                {
                    if (piece.side)
                        moves = board.player1.GetMovesForPiece(piece);
                    else
                        moves = board.player2.GetMovesForPiece(piece);
                }
                foreach (Move move in moves)
                {
                    int destinationKey = move.GetRow() * Board.WIDTH + move.GetCol();
                    graph[key].Add(destinationKey);
                }
            }
        }

        public void UpdateGraph(Move move)
        {
            int originKey = move.GetOrigin().row * Board.WIDTH + move.GetOrigin().col;
            int destinationKey = move.GetRow() * Board.WIDTH + move.GetCol();
            empty.Add(originKey, new Tuple<int, int>(move.GetOrigin().row, move.GetOrigin().col));
            empty.Remove(destinationKey);

            // Update origin piece's edges
            graph[originKey].Clear();
            List<Move> nearMoves = board.player1.GetNearMoves(board.GetPieceFromKey(originKey));
            foreach (Move nearMove in nearMoves)
            {
                int nearDestinationKey = nearMove.GetRow() * Board.WIDTH + nearMove.GetCol();
                graph[originKey].Add(nearDestinationKey);
            }
            
            // Update destination piece's edges
            List<Move> newMoves;
            if (board.GetPieceFromKey(destinationKey).side)
                newMoves = board.player1.GetMovesForPiece(board.GetPieceFromKey(destinationKey));
            else
                newMoves = board.player2.GetMovesForPiece(board.GetPieceFromKey(destinationKey));

            foreach (Move newMove in newMoves)
            {
                int newDestinationKey = newMove.GetRow() * Board.WIDTH + newMove.GetCol();
                if (!graph[destinationKey].Contains(newDestinationKey))
                {
                    graph[destinationKey].Add(newDestinationKey);
                }
            }
            // Check for new possible moves for other pieces on the board
            CheckForNewMoves();
        }

        public void CheckForNewMoves()
        {
            foreach (int pieceKey in graph.Keys)
            {
                Piece piece = board.GetPieceFromKey(pieceKey);
                List<Move> newMoves;
                if (piece == null)
                {
                    piece = new Piece(empty[pieceKey].Item1, empty[pieceKey].Item2);
                    newMoves = board.player1.GetNearMoves(piece);
                }
                else
                {
                    if (piece.side)
                        newMoves = board.player1.GetMovesForPiece(piece);
                    else
                        newMoves = board.player2.GetMovesForPiece(piece);
                }

                // Check for new possible destinations
                foreach (Move newMove in newMoves)
                {
                    int newDestinationKey = newMove.GetRow() * Board.WIDTH + newMove.GetCol();
                    if (!graph[pieceKey].Contains(newDestinationKey))
                    {
                        graph[pieceKey].Add(newDestinationKey);
                    }
                }
            }
        }

        public List<int> ShortestPathDijkstra(int startKey, int endKey)
        {
            // Create a priority queue to hold the unvisited nodes
            PriorityQueue unvisited = new PriorityQueue();

            // Create a dictionary to hold the distances from the start node to each node
            Dictionary<int, int> distances = new Dictionary<int, int>();

            // Create a dictionary to hold the previous node in the shortest path to each node
            Dictionary<int, int> previous = new Dictionary<int, int>();

            // Initialize the distances and previous dictionaries and add the start node to the queue
            foreach (int key in graph.Keys)
            {
                distances[key] = int.MaxValue;
                previous[key] = -1;
            }
            distances[startKey] = 0;
            unvisited.Enqueue(startKey, 0);

            // While there are still unvisited nodes
            while (unvisited.Count() > 0)
            {
                // Dequeue the node with the smallest distance
                int currentKey = unvisited.Dequeue();

                // If we have reached the end node, we can construct the shortest path
                if (currentKey == endKey)
                {
                    List<int> shortestPath = new List<int>();
                    int current = endKey;
                    while (current != -1)
                    {
                        shortestPath.Add(current);
                        current = previous[current];
                    }
                    shortestPath.Reverse();
                    return shortestPath;
                }

                // Update the distances to the neighboring nodes
                foreach (int neighborKey in graph[currentKey])
                {
                    int newDistance = distances[currentKey] + 1;
                    if (newDistance < distances[neighborKey])
                    {
                        distances[neighborKey] = newDistance;
                        previous[neighborKey] = currentKey;
                        unvisited.Enqueue(neighborKey, newDistance);
                    }
                }
            }
            // If we have not found a path, return an empty list
            return new List<int>();
        }
    }
}
