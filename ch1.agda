module ch1 where

open import Data.Bool hiding (_xor_)

_xor_ : Bool → Bool → Bool
true xor bb = not bb
false xor bb = bb

data Day : Set where
  Monday Tuesday Wednesday Thursday : Day
  Friday Saturday Sunday : Day

nextDay : Day → Day 
nextDay Monday = Tuesday
nextDay Tuesday = Wednesday
nextDay Wednesday = Thursday
nextDay Thursday = Friday
nextDay Friday = Saturday
nextDay Saturday = Sunday
nextDay Sunday = Monday

data Suit : Set where
  ♥ ♠ ♦ ♣ : Suit

is_red : Suit → Bool
is ♥ red = true
is ♠ red = true
is _ red = false

