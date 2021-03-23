-- Nathaniel Monahan / ncm5jv
----------------------------------
universes u₁ u₂

def foldr 
  {α : Type u₁} 
  {β : Type u₂} 
  :
  β →             
  (α → β → β) →       
  (list α → β)
| b f list.nil := b
| b f (h::t) := f h (foldr b f t)
-----------------------------------

inductive dihedral_actions : Type
| r_0
| r_270
| r_180
| r_90
| H
| D'
| V
| D

open dihedral_actions

def Cayley_actions : dihedral_actions → dihedral_actions → dihedral_actions
| r_0         action          := action
| action          r_0         := action

| r_270    r_90     := r_0
| r_90     r_270    := r_0

| r_180    r_180    := r_0
| D       D       := r_0
| H H := r_0
| D'      D'      := r_0
| V   V   := r_0


| r_90     r_180    := r_270
| r_180    r_90     := r_270

| H D'      := r_270
| D'      H := r_270

| D       V   := r_270
| V   D       := r_270


| r_270    r_180    := r_90
| r_180    r_270    := r_90

| H D       := r_90
| D       H := r_90

| D'      V   := r_90
| V   D'      := r_90


| r_270    r_270    := r_180
| r_90     r_90     := r_180

| H V   := r_180
| V   H := r_180

| D'      D       := r_180
| D       D'      := r_180


| r_270    V   := D
| V   r_270    := D

| r_180    D'      := D
| D'      r_180    := D

| r_90     H := D
| H r_90     := D


| r_270    D'      := V
| D'      r_270    := V

| r_180    H := V
| H r_180    := V

| r_90     D       := V
| D       r_90     := V


| r_270    D       := H
| D       r_270    := H

| r_180    V   := H
| V   r_180    := H

| r_90     D'      := H
| D'      r_90     := H


| D       r_180    := D'
| r_180    D       := D'

| V   r_90     := D'
| r_90     V   := D'

| r_270    H := D'
| H r_270    := D'

def comp : list dihedral_actions →  dihedral_actions
| list.nil := r_0
| l := foldr r_0 Cayley_actions l