import matplotlib.pyplot as plt
import matplotlib.cbook as cbook
import numpy as np

data = np.genfromtxt('synth_times.csv', delimiter=',', skip_header=0,
                     skip_footer=0, names=['example_name', 'synth_time'])
fig = plt.figure()
ax1 = fig.add_subplot(111)

ax1.set_title("Synthesis times")
ax1.set_xlabel('Example name')
ax1.set_ylabel('Synthesis time')


ax1.plot(data['example_name'], data['synth_time'], color='r', label='Synthesis times')
