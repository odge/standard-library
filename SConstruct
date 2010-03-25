import os, glob, string

nodes = ['.']
dirs = []
vs = []

while nodes:
  node = nodes.pop()
  b = os.path.basename(node)
  if node.endswith('.v'):
    vs += [node]
  if os.path.isdir(node) and node != "./broken":
    dirs += [node]
    nodes += glob.glob(node + '/*')

Rs = ' -R CategoryTheory CategoryTheory -R DataStructures DataStructures'
  # Todo: This sucks. We'd like to use "-R . ''", but this doesn't work. See Coq bug 2263.
Rs_and_Is = Rs + ' -I .'

coqc = 'coqc -nois ' + Rs_and_Is + ' $SOURCE'

env = DefaultEnvironment(ENV = os.environ)

def add_glob(target, source, env):
  base, _ = os.path.splitext(str(target[0]))
  target.append(base + ".glob")
  return target, source

env.Append(BUILDERS =
  {'Coq' : Builder(
    action = coqc,
    suffix = '.vo',
    src_suffix = '.v',
    emitter = add_glob)})

vos = globs = []
for node in vs:
  vo, glob = env.Coq(node)
  vos += [vo]
  globs += [glob]

env.Command(env.Dir('coqdoc'), vs + vos + globs,
  [Mkdir('coqdoc'), 'coqdoc -utf8 --no-lib-name -d $TARGET' + Rs + ' '.join(vs)])

os.system('coqdep ' + Rs_and_Is + ' '.join(vs) + ' > deps')
ParseDepends('deps')

Alias('coqide', Command(['dummy'], [], 'coqide ' + Rs_and_Is + ' &'))

Default('CategoryTheory','DataStructures')

open('coqidescript', 'w').write('#!/bin/sh\ncoqide' + Rs_and_Is + '$@ \n')
