namespace ChineseCheckers.Model
{
    public class Edge
    {
        private Pair<Vertex> _vertices;

        public Pair<Vertex> Vertices
        {
            get
            {
                return _vertices;
            }
            set
            {
                _vertices = Vertices;
            }
        }

        public Edge(Vertex a, Vertex b)
        {
            _vertices = new Pair<Vertex>(a, b);
        }
        public Edge(Pair<Piece> p)
        {
            _vertices = new Pair<Vertex>(new Vertex(p.First), new Vertex(p.Last));
        }

        #region Overrides
        
        public override bool Equals(object obj)
        {
            if (!(obj is Edge))
            {
                return false;
            }
            return (_vertices.First.Equals(obj) && _vertices.Last.Equals(obj));
        }

        public override int GetHashCode()
        {
            return _vertices.First.GetHashCode() * 23 + _vertices.Last.GetHashCode();
        }
        #endregion
    }
}