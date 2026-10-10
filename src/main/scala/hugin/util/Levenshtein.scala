package hugin.util

/** The edit distance used for suggestions ("did you mean"): the Levenshtein distance, the fewest
 *  insertions, deletions and substitutions of single characters (UTF-16 code units, as `String.charAt`
 *  counts them) that turn one string into the other. */
object Levenshtein:
  def distance(a: String, b: String): Int =
    if a.isEmpty then b.length
    else if b.isEmpty then a.length
    else
      // one row of the table: row(j) is the distance between the prefix of `a` read so far and b.take(j)
      val row = Array.tabulate(b.length + 1)(identity)
      var i = 1
      while i <= a.length do
        var diagonal = row(0)
        row(0) = i
        var j = 1
        while j <= b.length do
          val above = row(j)
          val cost = if a.charAt(i - 1) == b.charAt(j - 1) then 0 else 1
          row(j) = (row(j - 1) + 1).min(above + 1).min(diagonal + cost)
          diagonal = above
          j += 1
        i += 1
      row(b.length)
