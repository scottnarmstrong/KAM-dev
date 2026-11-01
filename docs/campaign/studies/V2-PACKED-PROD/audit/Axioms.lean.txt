module

public import LG00P.TP.Jet.Low.ChainCert
public import LG00P.TP.Jet.Full.ChainCert

/-! # Axioms of the packed jet chains of T′ (V2-PACKED-PROD receipt; not part of the format) -/

open KAM.CertificateSharp.Packed LG00P.TP

#print axioms jetLow_check
#print axioms jetLow_check_cert
#print axioms jetFull_check
#print axioms jetFull_check_cert
#print axioms jetPacked_sound
#print axioms jetPacked_sound_prefix
#print axioms jetCheck_of
#print axioms jChainK_slot
#print axioms jetChainOk_sound
#print axioms orderOk_spec
