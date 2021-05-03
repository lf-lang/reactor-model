import data.seq.seq
import data.vector

variable α : Type*

lemma single_kahn_process_deterministic (F : seq α → seq α) (s₁ s₂ : seq α) : s₁ = s₂ → F s₁  = F s₂ :=
begin
intro eq,
rw eq,
end

lemma comp_single_kahn_processes_deterministic (F G : seq α → seq α) (s₁ s₂ : seq α) : s₁ = s₂ → G (F s₁) = G (F s₂) :=
begin
intro eq,
rw eq,
end

variables n m p : ℕ
--variables s₁ s₂ : vector (seq α) n
--variables t₁ t₂ : vector (seq α) m

lemma multi_channel_kpn_det  (s₁ : vector (seq α) m) (s₂ : vector (seq α) m)
(F : vector (seq α) m → vector (seq α) n) : s₁ = s₂ → (F s₁ = F s₂) :=
begin
intro eq,
rw eq,
end

lemma comp_multi_channel_kpns_det  (s₁ : vector (seq α) m) (s₂ : vector (seq α) m)
(F : vector (seq α) m → vector (seq α) n) (G : vector (seq α) n → vector (seq α) p):
s₁ = s₂ → (G (F s₁) = G (F s₂)) :=
begin
intro eq,
rw eq,
end

