
data CapType = TLin | TNon | TRev | TSealed | TUninit 
    deriving (Eq)

type Addr = Int

data Perm = PermNA | PermR | PermRW | PermRX | PermRWX
    deriving (Eq)

data Reg = Pc | Sc | Ret | GPR Int

data MWord = Cap {
    capType :: CapType,
    capBase :: Addr,
    capEnd :: Addr,
    capCursor :: Addr,
    capPerm :: Perm,
    capNode :: Int 
} | Value Int | Inst Instruction

data RegFile = RegFile {
    pc :: MWord,
    sc :: MWord,
    ret :: MWord,
    gprs :: [MWord]
}

data RevNode = RevNode Int | RevNodeRoot | RevNodeNull

data RevTree = RevTree [RevNode]

data Instruction = Mov Reg Reg | Ld Reg Reg | Sd Reg Reg |
    Jmp Reg | Seal Reg | Call Reg | Lin Reg | Delin Reg | Drop Reg |
    Mrev Reg Reg | Tighten Reg Reg | Li Reg Int | Add Reg Reg |
    Lt Reg Reg Reg | Jnz Reg Reg | Split Reg Reg | Shrink Reg Reg Reg |
    Init Reg

data Mem = Mem [MWord]

data State = State RegFile Mem RevTree | Error

-- Zero out a given word if it is a linear capability
moved :: MWord -> MWord
moved w =
    case w of
        Cap t b e a p n -> 
            if t `elem` [TLin, TRev, TSealed, TUninit] then
                Value 0
            else
                w
        _ -> w

getReg :: RegFile -> Reg -> MWord
getReg regs r =
    case r of
        Pc -> pc regs
        Sc -> sc regs
        Ret -> ret regs
        GPR n -> (gprs regs) !! n

setReg :: RegFile -> Reg -> MWord -> RegFile
setReg regs r w =
    case r of
        Pc -> regs { pc = w }
        Sc -> regs { sc = w }
        Ret -> regs { ret = w }
        -- trick to replace an individual element by its index
        GPR n -> regs { gprs = (take n oldGPRs) ++ [w] ++ (drop (n + 1) oldGPRs) }
            where oldGPRs = gprs regs

incrementPC :: RegFile -> RegFile
incrementPC regs =
    setReg regs Pc newPC
        where 
            newPC = case oldPC of 
                Cap {} -> oldPC { capCursor = (capCursor oldPC) + 1 }
                _ -> Value 0
                where oldPC = getReg regs Pc

execMov :: State -> Reg -> Reg -> State
execMov st rd rs =
    case st of
        State regs mem rt -> 
            State (incrementPC (setReg (setReg regs rd w) rs (moved w))) mem rt
            where
                w = getReg regs rs 
        Error -> Error

readableCap :: MWord -> Bool
readableCap c =
    case c of
        Cap {} -> (capPerm c) `elem` [PermR, PermRX, PermRWX] && (capType c) /= TUninit
        _ -> False

writableCap :: MWord -> Bool
writableCap c =
    case c of
        Cap {} -> (capPerm c) `elem` [PermRW, PermRWX]
        _ -> False

executableCap :: MWord -> Bool
executableCap c =
    case c of
        Cap {} -> (capPerm c) `elem` [PermRX, PermRWX] && (capType c) /= TUninit
        _ -> False 

getRevNode :: RevTree -> Int -> RevNode
getRevNode rt n = RevNodeNull
    -- TODO: not implemented

revokedCap :: RevTree -> RevNode -> Bool
revokedCap rt rn =
    case rn of
        RevNodeRoot -> False
        RevNodeNull -> True
        RevNode n -> revokedCap rt parent where parent = getRevNode rt n
    

validCap :: RevTree -> MWord -> Bool
validCap rt c =
    case c of
        Cap _ _ _ _ _ rnid -> not (revokedCap rt rn) where rn = getRevNode rt rnid
        _ -> False

execute :: State -> Instruction -> State
execute st insn =
    case insn of
        Mov rd rs -> execMov st rd rs
        _ -> Error

main :: IO ()

main = do
    putStrLn("Ok")

