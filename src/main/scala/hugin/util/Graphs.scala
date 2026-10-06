package hugin.util

import scala.collection.mutable

/** Tarjan's strongly connected components algorithm (iterative). */
object Tarjan:
  /** Strongly connected components in reverse topological order (dependencies first). */
  def components[N](nodes: List[N], succ: N => List[N]): List[List[N]] =
    val index = mutable.HashMap.empty[N, Int]
    val low = mutable.HashMap.empty[N, Int]
    val onStack = mutable.HashSet.empty[N]
    val stack = mutable.Stack.empty[N]
    val out = mutable.ListBuffer.empty[List[N]]
    var i = 0
    val known = nodes.toSet
    def strong(v: N): Unit =
      // iterative to avoid deep recursion on long chains
      val work = mutable.Stack.empty[(N, Iterator[N])]
      def push(n: N): Unit =
        index(n) = i; low(n) = i; i += 1
        stack.push(n); onStack += n
        work.push((n, succ(n).iterator.filter(known)))
      push(v)
      while work.nonEmpty do
        val (n, it) = work.top
        if it.hasNext then
          val w = it.next()
          if !index.contains(w) then push(w)
          else if onStack(w) then low(n) = low(n).min(index(w))
        else
          work.pop()
          if work.nonEmpty then
            val parent = work.top._1
            low(parent) = low(parent).min(low(n))
          if low(n) == index(n) then
            val comp = mutable.ListBuffer.empty[N]
            var w: N = null.asInstanceOf[N]
            while
              w = stack.pop()
              onStack -= w
              comp += w
              w != n
            do ()
            out += comp.toList.reverse
    for n <- nodes if !index.contains(n) do strong(n)
    out.toList
