using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace ChineseCheckers.Model
{
    class PriorityQueue
    {
    private List<Tuple<int, int>> data;

    public PriorityQueue()
    {
        this.data = new List<Tuple<int, int>>();
    }

    public void Enqueue(int key, int priority)
    {
        data.Add(Tuple.Create(key, priority));
        int ci = data.Count - 1; // child index; start at end
        while (ci > 0)
        {
            int pi = (ci - 1) / 2; // parent index
            if (data[ci].Item2 >= data[pi].Item2) break; // child item is larger or equal than (or equal)
            Tuple<int, int> tmp = data[ci]; data[ci] = data[pi]; data[pi] = tmp;
            ci = pi;
        }
    }

    public int Dequeue()
    {
        // assumes pq is not empty; up to calling code
        int li = data.Count - 1; // last index (before removal)
        int frontItem = data[0].Item1;   // fetch the front
        data[0] = data[li];
        data.RemoveAt(li);

        --li; // last index (after removal)
        int pi = 0; // parent index. start at front of pq
        while (true)
        {
            int ci = pi * 2 + 1; // left child index of parent
            if (ci > li) break;  // no children so done
            int rc = ci + 1;     // right child
            if (rc <= li && data[rc].Item2 < data[ci].Item2) // if there is a rc (ci + 1), and it is smaller than left child, use the rc instead
                ci = rc;
            if (data[pi].Item2 <= data[ci].Item2) break; // parent is smaller than (or equal to) smallest child so done
            Tuple<int, int> tmp = data[pi]; data[pi] = data[ci]; data[ci] = tmp; // swap parent and child
            pi = ci;
        }
        return frontItem;
    }

    public int Count()
    {
        return data.Count;
    }
}


}
