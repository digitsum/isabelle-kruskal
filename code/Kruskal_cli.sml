open Kruskal

exception FAILED

fun fail msg = (print (msg ^ "\n"); raise FAILED)

fun
  the_fail NONE msg = fail msg
| the_fail (SOME x) msg = x

val int_of_gi = IntInf.toInt o Kruskal.integer_of_int
val gi_of_int = Int_of_integer o IntInf.fromInt
val int_of_gn = IntInf.toInt o integer_of_nat
val gn_of_int = nat_of_integer o IntInf.fromInt


fun readList (infile : string) = let
  val ins = TextIO.openIn infile
  fun loop ins =
   case TextIO.inputLine ins of
      NONE      => []
    | SOME line => line :: loop ins
in
  let
    fun parse_integer s = case Int.fromString s of
      SOME i => i
    | NONE => fail ("Expected integer, but got '" ^ s ^"'")

    val parse_int = gi_of_int o parse_integer
    val parse_nat = gn_of_int o parse_integer

    val tokenize = String.tokens (fn c => c = #" ")

    fun parse_edge s = let
      val l = tokenize s
    in
      case l of
        [a,b,w] => (parse_nat a, (parse_int w, parse_nat b))
      | _ => fail ("Expected edge in format 'a b w', but got " ^ s)
    end

    fun parse_graph edges = map parse_edge edges

    val lines = (loop ins before TextIO.closeIn ins)

  in
    parse_graph lines
  end
end

fun print_graph edges = let
  val parse_int = IntInf.toString o int_of_gi
  val parse_nat = IntInf.toString o int_of_gn

  fun print_edge (a, (w, b)) =
    print(parse_nat a ^ " " ^ parse_nat b ^ " " ^ parse_int w ^ "\n")
in
  map print_edge edges
end

fun main () = let
  val args = CommandLine.arguments ();

  fun perform G = let
    val res_list = kruskal G ()
  in
    print("Input graph:\n");
    print_graph G;
    print("Minimum spanning forest:\n");
    print_graph res_list;
    print("Number of edges: " ^ IntInf.toString (length res_list) ^ "\n");
    ()
  end

in
  case args of
    [gname] => let
      val G = readList gname
    in
      perform G
    end
    | _ => print "Usage: Kruskal <file-name>"
end

val _ = if MLton.isMLton then main() else ()
