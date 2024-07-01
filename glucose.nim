import std/[macros, sugar, strformat, macrocache]

## We use a `CacheSeq` to pass the untyped symbols from
## the `:=` macro to the `assignImpl` macro. Because we need
## to go from `untyped -> typed` we cannot pass them directly.
const Args = CacheSeq"ArgSeq"

proc countArgs(n: NimNode): int =
  ## Count the number of arguments the given symbol of a proc has
  doAssert n.kind == nnkProcTy
  let p = n.params
  if p[0].kind != nnkEmpty: inc result
  for i in 1 ..< p.len:
    inc result, p.len - 2 # multiple arguments of same type are in one `nnkIdentDefs`.
                          # -> 1 arg of a type: `nnkIdentDefs.len == 3`, else `3 + n`

proc produceCall(call: NimNode, cArgs, lhsArgs: seq[NimNode]): NimNode =
  ## Produce the variable derclarations based on the types the symbol `call`
  ## has and the given arguments
  ##
  ## - `cArgs`: the arguments `call()` already has in the `:=` RHS
  ## - `lhsArgs`: the argument of the `:=` on the LHS.
  ##   -> If `call` returns a value `lhsArgs[0]` is the new variable we
  ##   use for the return value. All other variables are interpreted as
  ##   `out` parameters of `call`.
  ##
  ## The combined number of `cArgs.len + lhsArgs.len` was used in `assignImpl`
  ## to determine the overload of `call`, if any.
  doAssert call.kind == nnkSym
  # get directly
  let impl = call.getTypeImpl
  doAssert impl.kind == nnkProcTy
  let p = impl.params
  let hasResult = p[0].kind != nnkEmpty

  # handle arguments
  var lIdx = if hasResult: 1 else: 0 # lhsArgs index
  var cIdx = 0 # cArgs index
  var cNode = nnkCall.newTree(call)
  var lhsTypes = newSeq[NimNode]() # types for each `lhsArgs`
  for i in 1 ..< p.len:
    # if we encounter an `out` param:
    #   IdentDefs
    #     Sym "y"
    #     VarTy       <------ `out` param
    #       Sym "int"
    #     Empty
    # fill with next `cArgs`
    let arg = p[i]
    doAssert arg.kind == nnkIdentDefs, "??? : " & $arg.treerepr
    if arg[1].kind == nnkVarTy: # replace
      cNode.add lhsArgs[lIdx]
      inc lIdx
      lhsTypes.add arg[1][0] #
    else:
      # use `cArgs`
      cNode.add cArgs[cIdx]
      inc cIdx

  # produce the `var` section
  var vars = nnkVarSection.newTree()
  # debugEcho lhsTypes.repr
  # debugEcho lhsArgs.repr

  for i, arg in lhsArgs:
    if hasResult and i == 0: continue
    let idx = if hasResult: i - 1 else: i
    vars.add nnkIdentDefs.newTree(
      arg,
      lhsTypes[idx],
      newEmptyNode()
    )

  if hasResult: # overwrite `cNode` to be `var foo = theCall(args)`
    cNode = nnkVarSection.newTree(
      nnkIdentDefs.newTree(
        lhsArgs[0],
        newEmptyNode(),
        cNode
      )
    )

  # debugEcho vars.repr
  # debugEcho cNode.repr

  result = newStmtList()
  result.add vars
  result.add cNode
  # debugEcho result.treerepr
  # debugEcho "RESULT:: ", result.repr, "||"

macro assignImpl(call: typed, args: typed, startIdxN: int): untyped =
  ## Extracts symbols from `Args` (for the LHS untyped symbols) and
  ## determines the correct overload of `call` (if any) based on
  ##
  ## - Number of elements in `Args` from `startdIdxN`
  ## - number of `args` elements, i.e. the explicit arguments already
  ##   given to `call` on the RHS in `:=`

  # extract symbols from `Args`
  var syms = newSeq[NimNode]()
  let startIdx = startIdxN.intVal
  for i in startIdx ..< Args.len:
    let arg = Args[i]
    syms.add arg
  # turn `args` into a `seq` so we can pass it down nicer
  var cArgs = newSeq[NimNode]() # arguments already present on RHS
  for c in args:
    cArgs.add c

  # compute number of total arguments to determine overload
  let numArgs = syms.len # number of arguments on LHS, possibly +1 if  `call` returns something
  let totalArgs = numArgs + args.len # total arguments needed for an overload to match

  case call.kind
  of nnkOpenSymChoice, nnkClosedSymChoice:
    # determine based on # of arguments
    for ch in call:
      let impl = getTypeImpl(ch)
      if countArgs(impl) == totalArgs:
        return produceCall(ch, cArgs, syms)
  of nnkSym:
    result = produceCall(call, cArgs, syms)
  else:
    raiseAssert "Unsupported: " & $call.kind

macro `:=`(lhs, call: untyped): untyped =
  ## Go like declaration + assignment operator.
  ## If `call` has `out` parameters, use a tuple on the
  ## LHS,
  ##
  ## `(x, err) = foo(5)` # where
  ## `proc foo(x: int, err: out int)`
  ## or
  ## `proc foo(err: out int, x: int)`
  ## the right position is determined automatically.
  ##
  ## Declares `x` and `err` in your code's scope.

  if call.kind == nnkCall:
    # get symbols for out parameters from LHS
    let StartIdx = Args.len # fill the real arguments to `Args` to "pass" them as untyped
    for arg in lhs:
      Args.add arg
    result = newStmtList()

    # The arguments currently given to `call`
    var args = nnkBracket.newTree()
    for i in 1 ..< call.len:
      args.add call[i]

    # pass to the `typed` macro
    let callSym = call[0] # the actual fn on the RHS
    result.add quote do:
      assignImpl(`callSym`, `args`, `StartIdx`)
    # debugEcho result.repr

  elif len(lhs) == 0 and len(call) == 0:
    result = quote do:
      var `lhs` = `call`
    # debugEcho result.repr

  elif call.kind in {nnkTupleConstr} and len(lhs) == len(call):
    result = newStmtList()
    for i in 0..<len(lhs):
      result.add newVarStmt(lhs[i], call[i])
    # debugEcho result.repr

  else:
    error(fmt"Invalid expression {lhs.repr} := {call.repr}")

proc foo(): int = 5

proc baz(x: int, y: out int): int =
  y = 2 * x
  if y < 0:
    result = -1


proc bar(x: out int, y: int) : int =
  x = y div 2
  if x < 1:
    result = -1

block:
  echo "baz(5) => (10, 0)"
  (err, res) := baz(5)
  dump res
  dump err

block:
  echo "baz(-1) => (-2, -1)"
  (err, res) := baz(-1)
  dump res
  dump err

block:
  echo "bar(5) => (0, 2)"
  (err, res) := bar(5)
  dump res
  dump err

block:
  echo "bar(1) => (-1, 0)"
  (err, res) := bar(1)
  dump res
  dump err

block:
  X := 36
  dump X

block:
  (X, Y, Z) := ("Hello world", 36.66, 46)
  dump X
  dump Y
  dump Z

