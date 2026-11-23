module

import DY.Meta
import DY.Meta.Utils
import Examples.HPKE.Specification
import Examples.HPKE.Instance
public meta import Examples.HPKE.Instance

namespace DY.Example.HPKE


private
def firstSealPtFrom (tr: ExecTrace) (i fuel: Nat): Option Bytes :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match tr.getEventAt HPKEAuthEvent i with
    | some (.SealEvent _ _ _ _ pt) => some pt
    | _ => firstSealPtFrom tr (i + 1) fuel

/--
Returns the plaintext carried by the first `SealEvent` in the trace, if any.
-/
private
def firstSealPt (tr: ExecTrace): Option Bytes :=
  firstSealPtFrom tr 0 tr.length

private
def firstOpenPtFrom (tr: ExecTrace) (i fuel: Nat): Option Bytes :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match tr.getEventAt HPKEAuthEvent i with
    | some (.OpenEvent _ _ _ _ pt) => some pt
    | _ => firstOpenPtFrom tr (i + 1) fuel

/--
Returns the plaintext carried by the first `OpenEvent` in the trace, if any.
-/
private
def firstOpenPt (tr: ExecTrace): Option Bytes :=
  firstOpenPtFrom tr 0 tr.length

/--
Baseline honest end-to-end HPKE run used as a sanity check.

Flow:
1. Generate Alice and Bob long-term key pairs.
2. Alice seals a message to Bob.
3. Bob opens the resulting ciphertext.

The accompanying `#guard` checks that the first logged `SealEvent` plaintext
matches the first logged `OpenEvent` plaintext in the resulting trace.
-/
public
def honestAttacker: Traceful Unit := do
  let (_, senderPkHandle, senderSkHandle) ← LongTermKeys.generateKeyPair "HPKE Auth PKI" "Alice"
  let (_, recipientPkHandle, recipientSkHandle) ← LongTermKeys.generateKeyPair "HPKE Auth PKI" "Bob"
  let msgHandle ← Sender.seal "Alice" "Bob" senderSkHandle recipientPkHandle
  let _ ← Recipient.open "Bob" "Alice" recipientSkHandle senderPkHandle msgHandle
  return ()

#guard (
  let run := honestAttacker.run Trace.nil
  match firstSealPt run.snd.1, firstOpenPt run.snd.1 with
  | some sealPt, some openPt => sealPt = openPt
  | _, _ => False
)

/--
Adversarial scenario where the recipient long-term private key is compromised
after ciphertext creation, then used to decrypt the message off-protocol.

Flow:
1. Generate Alice and Bob long-term key pairs.
2. Alice seals a message to Bob.
3. Compromise Bob's private key state via `LongTermKeys.compromisePrivateKey`.
4. Parse the leaked state and recover Bob's secret key.
5. Reconstruct decryption inputs from network messages and decrypt manually.

The accompanying `#guard` checks that the recovered plaintext equals the
plaintext in the first logged `SealEvent`.
-/
public
def compromiseRecipientLtkAttacker: Traceful Bytes := do
  let (senderPkMsgHandle, _, senderSkHandle) ← LongTermKeys.generateKeyPair "HPKE Auth PKI" "Alice"
  let (_, recipientPkHandle, recipientSkHandle) ← LongTermKeys.generateKeyPair "HPKE Auth PKI" "Bob"

  let msgHandle ← Sender.seal "Alice" "Bob" senderSkHandle recipientPkHandle

  let compromiseHandle ← LongTermKeys.compromisePrivateKey "HPKE Auth PKI" recipientSkHandle
  let recipientSkStBytes ← Network.receiveMessage compromiseHandle
  let recipientSkSt: PersistentLocalState.LocalState (LongTermKeys.SecretKeyState "HPKE Auth PKI") ← Comparse.parse recipientSkStBytes
  let recipientSk := recipientSkSt.state.sk

  let senderPk ← Network.receiveMessage senderPkMsgHandle
  let msgBytes ← Network.receiveMessage msgHandle
  let msg: CiphertextMessage ← Comparse.parse msgBytes
  let sharedSecret ← AKEM.kemDecap recipientSk senderPk msg.enc
  let key := deriveKey sharedSecret
  let nonce := deriveNonce sharedSecret
  let openedPt ← (show Err Bytes from AEAD.aead_dec key nonce msg.aad msg.ct)

  return openedPt

#guard (
  let run := compromiseRecipientLtkAttacker.run Trace.nil
  match run.fst, firstSealPt run.snd.1 with
  | some openedPt, some sealPt => openedPt = sealPt
  | _, _ => False
)


end DY.Example.HPKE
