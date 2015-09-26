module Monads



(* 

To Define a monad we must do 3 things:

(A) First define the monad type M<'T>.
In the case of the maybe monad the monad type is the Option<'T>
// i.e. Monad type : M<'T> = Option<'t>

(B)A bind function where 
 - first argument is a value in a monadic type, 
 - its second argument is a function that maps from the underlying type of the first argument to another monadic type
 - and its result is in that other monadic type.
Bind : M<'T> * ('T -> M<'U>) -> M<'U>

(C) a return function (called by return)
that maps a value of the underlying type to a value in the corresponding monadic type
Return : 'T -> M<'T>

================     F# compiler transformation ===============================

let m:M<U> = mymonad {
    let! x:T = Some expression that evaluates to M<T>
    ...
    Some othe code that uses x and produces the final result u:of type U
    ...
    return u
}

every let! is transformed to a call to bind where 
 - the first argument is what is right of the = in the let! 
    i.e. the Some expression that evaluates to M<T>
 - the second argument is a lamda that takes as input the let! name (x in our case). 
   The body of the lamda is the rest of code until we reach the end 
   of our monad. If the rest code contains another let! expression then this
   is also replaced by a call to bind etc. 
   finally return (expr) is transformed to a mymonad.Return (expr)

================ The above pseudp code is transformed to the followinf code ===========

let m:M<U> = 
    mymonad.bind(
        (Some expression that evaluates to M<T>),
        (
            fun x   ->
                ...
                Some othe code that uses x and produces the final result u:of type U
                ...
                mymonad.return u
        )
    )

*)




(* Maybe monad *)
(*A Monad Type Definition*)

type Maybe<'T> = Option<'T>

type MaybeBuilder() =
  member this.Return a = Some a
  member this.Bind(m:Maybe<'T>, f:('T -> Maybe<'K>)):Maybe<'K> = 
    match m with
    | None  -> None
    | Some t -> f t

let maybe = new MaybeBuilder()


(* State monad*)

type State<'T, 'State> = ('State -> 'T * 'State)


type StateBuilder() =
  member this.Return a = (fun s -> a,s)
  member this.Bind(m:State<'T, 'State>, f:('T -> State<'K, 'State>)):State<'K, 'State> = 
    (fun s ->
        let t, s1 = m s
        f t s1 )
let getState = (fun s -> s,s)
let setState s = (fun _ -> (),s)

let state = new StateBuilder()

let rec smap func  lst =
    state {
        match lst with
        | []        ->  return []
        | h::tail   -> 
            let! procItem = func h
            let! restList = tail |> smap func 
            return procItem::restList
    }

let smapi func  lst =
    let rec smapi_aux func  idx lst =
        state {
            match lst with
            | []        ->  return []
            | h::tail   -> 
                let! procItem = func idx h
                let! restList = tail |> smapi_aux func (idx+1)
                return procItem::restList
        }
    let ret = smapi_aux func  0 lst
    ret




type ContinuationBuilder() = 
    member this.Return(x) = (fun k -> k x) 
    member this.ReturnFrom(x) = x 
    member this.Bind(m,f) = (fun k -> m (fun a -> f a k)) 
    member this.Delay(f) = (fun k -> f () k) 
let cont = new ContinuationBuilder()

let mmap f xs = 
           let rec MMap' (f, xs', out) = 
               cont {
                       match xs' with
                       | h :: t -> let! h' = f(h)
                                   return! MMap'(f, t, List.append out [h'])
                       | [] -> return out
                    }
           MMap' (f, xs, [])


let mfold f acc xs =
          let rec Mfold' (f, xs', acc') = 
               cont {
                       match xs' with
                       | h :: t -> let! h' = f h acc'
                                   return! Mfold'(f, t, h')
                       | [] -> return acc'
                    }
          Mfold' (f, xs, acc)

type TreeLeafNode = {
        name: string
        uniqueId: int
    }

type Tree =
| Leaf of TreeLeafNode
| Branch of Tree * Tree

let CTN s = {TreeLeafNode.name = s; uniqueId=0}



let tree =
  Branch(
    Leaf (CTN "Max"),
    Branch(
      Leaf (CTN "Bernd"),
      Branch(
        Branch(
          Leaf (CTN "Holger"),
          Leaf (CTN "Ralf")),
        Branch(
          Leaf (CTN "Kerstin"),
          Leaf (CTN "Steffen")))))

let rec populateTree (t:Tree) : State<Tree, int>=
    state {
        match t with
        | Leaf node ->
            let! curState = getState
            let newNode = {node with uniqueId =curState}
            do! setState(curState+1)
            return (Leaf newNode)
        | Branch(left,right) ->
            let! nl = populateTree left
            let! nr = populateTree right
            return Branch(nl, nr)
    }





let test_main argv = 

    let list1 = [0;0;0]

    let handleInt x = 
        state {
            let! (curState:int) = getState
            do! setState (curState+1)
            return (x+curState)
        }

    let newList = 
        state {
           let! retList =  list1 |> smap handleInt
           return retList }
    let finalList = newList 1 |> fst

    let someFuncReturningIntOption1 () =
        Some 1
    let someFuncReturningIntOption2 () =
        Some 2

    let res = maybe {
        let! a1 = someFuncReturningIntOption1 ()
        let! a2 = someFuncReturningIntOption2 ()
        return a1+a2
    }

    let res1 =
        maybe.Bind(  
            someFuncReturningIntOption1 (),
            (fun a1 ->
                maybe.Bind( 
                    someFuncReturningIntOption2 (),
                    (fun a2 -> 
                        maybe.Return (a1+a2))))
        )

            
        

    printfn "%A" res
    printfn "%A" res1

    

    printfn "%A" tree


    let tree2 = (populateTree tree) 0 |> fst
    printfn "%A" tree2

    0 // return an integer exit code
