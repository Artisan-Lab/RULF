?=1
until [[ $? -eq 0 ]]; do
git submodule update;
done