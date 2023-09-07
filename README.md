## A formal verification of the IFF authentication protocol

You can find in this repository:
- `iff.cafe`: The formal specification of the IFF authentication protocol and the properties for the verification. The detailed explanation is given below.
- `inputs`: Input scripts for IPSG to produce the proof scores.
- other files: The proof scores of the properties.

---
### IFF protocol
IFF is used to check if a principal is a member of a
group. The IFF protocol can be described as the following
two message exchanges:

Check   A -> B : r

Reply   B -> A : enc(k, r || B)

where r is a random value and k is the key of the group B belongs to.

---
### CafeOBJ Specification
Module `PRINCIPAL` specifies protocol participants. `intru` denotes the Dolev-Yao intruder.

```
mod* PRINCIPAL {
  [Prin]
  op intru : -> Prin {constr}
}
```

Module `KEY` specifies group keys. Given a principal `a`, `gk(a)` denotes the key of the group `a` belongs to. We suppose that there are only two group: one honest group and one dishonest group, where the latter consists of only `intru`.
```
mod* KEY {
  pr(PRINCIPAL)
  [Key]
  op gk : Prin -> Key {constr}
  vars P P2 : Prin
  vars K K2 : Key
  ceq (gk(P) = gk(intru)) = false if not(P = intru) .
  ceq (gk(P) = gk(P2)) = true if not(P = intru) and not(P2 = intru) .
}
```

Sort `Rand` represents the random values:
```
mod* RANDOM {
  [Rand]
}
```

We introduce module `DATA` with sorts `Data` and `DataL` representing generic data types, i.e., the supersorts of all sorts introduced so far. `||` and `\in` are concatenation operator and membership operator, respectively.

```
mod! DATA {
  pr(PRINCIPAL + NONCE)
  [Data < DataL]
  [Prin PubKey PriKey Nonce < Data]
  op _||_  : DataL DataL -> DataL {assoc r-assoc constr}
  op _\in_ : DataL DataL -> Bool
```

The two operators are defined by some equations.
We also specify the equal of two terms of sort `Data`, for example:

```
  ceq (P = D1)  = false if (D1 :is Key) or 
                           (D1 :is Rand) .
```
specifies that any key, and random value cannot equal a principal.

We define encryption and decryption in module `ENCRYPTION`:

```
mod! ENCRYPTION {
  pr(DATA)
--         Key  Plaintext     Ciphertext
  op enc : Key  DataL      -> Data {constr}
--         Key  Ciphertext    Plaintext
  op dec : Key  Data       -> DataL
```

We specify the cancelation property of encryption and decryption:
```
  eq dec(K, enc(K,DL)) = DL .
  eq (dec(K, D2) = DL) = (D2 = enc(K,DL)) .
```

We specify that ciphertext of encryption cannot equal a principal, a random value, or a key:
```
  ceq (enc(K,DL) = D) = false if (D :is Prin) or 
                                 (D :is Rand) or
                                 (D :is Key) .
}
```

Module `MESSAGE` specifies messages exchanged in the protocol:
```
mod! MESSAGE {
  pr(ENCRYPTION)
  [Msg]
  op msg1 : Prin Prin Prin DataL -> Msg {constr}
  op msg2 : Prin Prin Prin DataL -> Msg {constr}
```

`init` represents all initial states. `send1` and `send2` specify a principal sends the Check and the Reply messages, respectively. Three observer `nw`, `urand`, and `knl` observing the network, the set of used randoms, and the knowledge of the intruder.

```
mod NSLPK {
  pr(NETWORK)
  pr(SET(D <= TRIV2DATA)*{sort Set -> RandSet})
  [Sys]

  op init : -> Sys {constr}
  op send1 : Sys Prin Prin Rand -> Sys {constr}
  op send2 : Sys Prin Prin Prin Rand -> Sys {constr}

  op nw : Sys -> Network
  op urand : Sys -> RandSet
  op knl : Sys -> DataL
```

The initial state is defined as follow:
```
  eq nw(init) = void .
  eq urand(init) = empty .
  eq knl(init) = gk(intru) .
```

Transition `send1` specifies principal `A` sends the Check message to principal `B`. Note that the used random `R` is also added to the intruder knowledge, meaning that the intruder gleans that random value.

```
  op c-send1 : Sys Rand -> Bool
  eq c-send1(S,R) = not(R \in urand(S)) .
  ceq nw(send1(S,A,B,R)) = 
      (msg1(A,A,B, R) , nw(S)) 
    if c-send1(S,R) .
  ceq urand(send1(S,A,B,R)) = (R urand(S)) 
    if c-send1(S,R) .
  ceq knl(send1(S,A,B,R)) = (R || knl(S)) 
    if c-send1(S,R) .
  ceq send1(S,A,B,R) = S 
    if not c-send1(S,R) .
```

Transition `send2` is defined similarly.

We turn to specify the intruder.
The intruder can randomly select a random `R` (which must be unused before), and added to its knowledge:

```
  op gRand : Sys Rand -> Sys {constr}
  op c-gRand : Sys Rand -> Bool
  eq c-gRand(S,R) = not(R \in urand(S)) .
  eq nw(gRand(S,R)) = nw(S) .
  ceq urand(gRand(S,R)) = (R urand(S))
    if c-gRand(S,R) .
  ceq knl(gRand(S,R)) = (R || knl(S))
    if c-gRand(S,R) .
  ceq gRand(S,R) = S 
    if not c-gRand(S,R) .
```

Any values of basic data types are known by the intruder:
```
  op gBasic : Sys Prin -> Sys {constr}
  eq nw(gBasic(S,A)) = nw(S) .
  eq urand(gBasic(S,A)) = urand(S) .
  eq knl(gBasic(S,A)) = (A || knl(S)) .
``` 

Given a key `K` and a piece of data `DL2`, which are available to the intruder, the intruder can encrypt `DL2` by `K` and learn the obtained ciphertext:
```
  op g2 : Sys Key DataL -> Sys {constr}
  op c-g2 : Sys Key DataL -> Bool
  eq c-g2(S,K,DL2) = (K \in knl(S) and DL2 \in knl(S)) .
  eq nw(g2(S,K,DL2)) = nw(S) .
  eq urand(g2(S,K,DL2)) = urand(S) .
  ceq knl(g2(S,K,DL2)) = 
      (enc(K,DL2) || knl(S)) 
    if c-g2(S,K,DL2) .
  ceq g2(S,K,DL2) = S if not c-g2(S,K,DL2) .
```

With this protocol, the intruder can decrypt a ciphertext only if they know the correct key:
```
  op g22 : Sys Key DataL -> Sys {constr}
  op c-g22 : Sys Key DataL -> Bool
  eq c-g22(S,K,DL2) = (K \in knl(S) and enc(K,DL2) \in knl(S)) .
  eq nw(g22(S,K,DL2)) = nw(S) .
  eq urand(g22(S,K,DL2)) = urand(S) .
  ceq knl(g22(S,K,DL2)) = (DL2 || knl(S)) 
    if c-g22(S,K,DL2) .
  ceq g22(S,K,DL2) = S if not c-g22(S,K,DL2) .
```

If a piece of data `D1` is available to the intruder, the intruder can use it as the ciphertext, pretend `A`, send it to `B` (the Reply message):
```
  op fkmsg2 : Sys Prin Prin Data -> Sys {constr}
  op c-fkmsg2 : Sys Prin Prin Data -> Bool
  eq c-fkmsg2(S,A,B,D1) = 
    (D1 \in knl(S)) .
  ceq nw(fkmsg2(S,A,B,D1)) = 
      (msg2(intru,A,B, D1) , nw(S))
    if c-fkmsg2(S,A,B,D1) .
  eq urand(fkmsg2(S,A,B,D1)) = urand(S) .
  eq knl(fkmsg2(S,A,B,D1)) = knl(S) .
  ceq fkmsg2(S,A,B,D1) = S 
    if not c-fkmsg2(S,A,B,D1) .
```

---
### Formal verification
In the module `PROPERTIES`,
the predicate `iden` specifies the *identifiable* propery of the protocol

```
  op iden : Sys Prin Prin Prin Rand Data -> Bool
  eq iden(S,A,B,B2,R,D) = 
    (not(A = intru) and
     msg1(A,A,B, R) \in nw(S) and
     msg2(B2,B,A, D) \in nw(S) and
     dec(gk(A), D) = R || B)
    implies not(B = intru) .
```
`iden` states that if initiator `A` has sent a Check message to `B` and received a Reply message apparently from `B` with a ciphertext `D` such that `A` can successfully decrypt `D` by using their group key, then `B` belongs to the same group of `A`, i.e., `B` does not belong to the intruder group.

`iden` is prove by induction with the employment of IPSG, where some auxilary lemmas are needed (precisely, `inv1` and `inv7`).
