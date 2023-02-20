using System;
using System.Collections.Generic;
using System.Drawing;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.Windows.Forms.VisualStyles;

namespace ChineseCheckers.Model
{
    public class Graph1
    {
        #region Instance Variables
        Board owner;
        //vertices should have quick access through usage of a hashmap
        private Dictionary<Vertex, bool> _vertices;
        private Dictionary<Edge, bool> _edges;

        public Vertex[] Vertices
        {
            get
            {
                return _vertices.Keys.ToArray<Vertex>();
            }
        }
        public Edge[] Edges
        {
            get
            {
                return _edges.Keys.ToArray<Edge>();
            }
        }

        #endregion


        #region Constructors
        /// <summary>
        /// Creates an empty Graph.
        /// </summary>
        public Graph1(Board owner)
        {
            this.owner = owner;
            _vertices = new Dictionary<Vertex, bool>();
            _edges = new Dictionary<Edge, bool>();
        }
        public void CreateGraph()
        {
            for (int i = 0; i < Board.HEIGHT; i++)
            {
                for (int j = 0; j < Board.WIDTH; j++)
                {
                    if (Board.initmat[i, j] != 0)
                    {
                        Piece piece = owner.getPiece(i, j);
                        if (piece == null)
                            piece = new Piece(i, j);
                        AddNewVertex(new Vertex(piece));
                    }
                }
            }

            foreach (KeyValuePair<Vertex, bool> vertex in _vertices)
            {
                Piece piece = vertex.Key.Piece;
                int[,] directions = { { -1, -1 }, { -1, 1 }, { 1, 1 }, { 1, -1 }, { 0, 1 }, { 0, -1 } } ;
                for (int i = 0; i < directions.Length / 2; i++)
                {
                    int row = piece.row + directions[i, 0];
                    int col = piece.col + directions[i, 1];
                    if (row >= 0 && row < Board.HEIGHT && col >= 0 && col < Board.WIDTH)
                    {
                        if (Board.initmat[row, col] != 0)
                        {
                            Piece otherPiece = owner.getPiece(row, col);
                            if (otherPiece == null)
                                otherPiece = new Piece(row, col);
                            Pair<Piece> pair = new Pair<Piece>(piece, otherPiece);
                            AddNewEdge(pair);
                        }
                    }
                }
            }
        }


        #endregion


        #region Add/Remove-Methods

        /// <summary>
        /// Adds a new Vertex with the specified name.
        /// Returns false when Vertex already existed.
        /// </summary>
        /// <param name="name"></param>
        /// <returns></returns>


        /// <summary>
        /// Adds the specified Vertex to the Graph.
        /// Returns false when Vertex already existed.
        /// </summary>
        /// <param name="vertex"></param>
        /// <returns></returns>
        public bool AddNewVertex(Vertex v)
        {
            if (!_vertices.ContainsKey(v))
            {
                _vertices.Add(v, true);
                return true;
            }
            return false;
        }

        /// <summary>
        /// Adds a new Edge between the two vertices defined by the strings.
        /// Returns false when edge already existed.
        /// </summary>
        /// <param name="a"></param>
        /// <param name="b"></param>
        /// <returns></returns>


        /// <summary>
        /// Adds a new Edge between the two vertices defined by the string-pair.
        /// Returns false when edge already existed.
        /// </summary>
        /// <param name="stringpair"></param>
        /// <returns></returns>
        public bool AddNewEdge(Pair<Piece> p)
        {
            return AddNewEdge(new Edge(p));
        }

        /// <summary>
        /// Adds the specified Edge to the Graph.
        /// Returns false when edge already existed.
        /// </summary>
        /// <param name="edge"></param>
        /// <returns></returns>
        public bool AddNewEdge(Edge newEdge)
        {
            if (!_edges.ContainsKey(newEdge) && !_edges.ContainsKey(new Edge(newEdge.Vertices.Last, newEdge.Vertices.First)))
            {
                Vertex firstV = newEdge.Vertices.First;
                Vertex lastV = newEdge.Vertices.Last;
                if (!_vertices.ContainsKey(firstV))
                {
                    AddNewVertex(firstV);
                }
                if (!_vertices.ContainsKey(lastV))
                {
                    AddNewVertex(lastV);
                }
                _edges.Add(newEdge, true);
                return true;
            }
            return false;
        }

        /// <summary>
        /// Removes the defined Edge from the Graph.
        /// Returns false when the Edge did not exist.
        /// </summary>
        /// <param name="edge"></param>
        /// <returns></returns>
        public bool RemoveEdge(Edge edge)
        {
            if (_edges.ContainsKey(edge))
            {
                _edges.Remove(edge);
                return true;
            }
            return false;
        }

        /// <summary>
        /// Removes the defined Vertex and all Edges containing it from the Graph.
        /// Returns false when the Vertex did not exist.
        /// </summary>
        /// <param name="vertex"></param>
        /// <returns></returns>
        public bool RemoveVertex(Vertex vertex)
        {
            if (!_vertices.ContainsKey(vertex))
            {
                return false;
            }
            foreach (Edge edge in _edges.Keys)
            {
                if (edge.Vertices.Contains(vertex))
                    _edges.Remove(edge);
            }
            _vertices.Remove(vertex);
            return true;
        }

        #endregion
    }
}
