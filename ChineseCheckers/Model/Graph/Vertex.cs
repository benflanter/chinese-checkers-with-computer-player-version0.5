namespace ChineseCheckers.Model
{
    public class Vertex
    {
        private Piece piece;
        
        public Piece Piece { get => piece; set => piece = value; }
        

        public Vertex(Piece piece)
        {
            this.piece = piece;
        }

        #region Overrides
        
        public override bool Equals(object obj)
        {
            if (!(obj is Vertex))
                return false;
            return ((Vertex)obj).piece == piece;
        }

        public override int GetHashCode()
        {
            if (piece == null)
                return 100;
            return piece.GetHashCode();
        }
        #endregion
    }
}